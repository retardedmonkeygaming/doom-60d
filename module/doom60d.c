#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#include <module.h>
#include <dryos.h>
#include <bmp.h>
#include <config.h>
#include <fio-ml.h>
#include <menu.h>
#include <timer.h>

#include "doomgeneric.h"
#include "m_menu.h"
#include "doomkeys.h"
#include "i_video.h"
#include "doomdef.h"
#include "d_main.h"
#include "d_player.h"
#include "doomstat.h"
#include "doom_audio_ml.h"
#include "doom_cheat_menu.h"
#include "doom_debug.h"
#include "m_config.h"
#include "p_saveg.h"

/* Resolution matches 60D / 550D screen */
#define DOOM_W 720
#define DOOM_H 480
#define DOOM_X ((720 - DOOM_W) / 2)
#define DOOM_Y ((480 - DOOM_H) / 2)

#define DOOM_LOG_FILE "ML/LOGS/DOOM60D.LOG"
#define DOOM_WAD_DIR "ML/DOOM/"
#define DOOM_SAVE_DIR "ML/DOOM/SAVES"
#define DOOM_CONFIG_DIR "ML/DOOM/CONFIG"
#define DOOM_MAX_WAD_FILES 32
#define DOOM_MAX_LOG_FILES 32

static CONFIG_INT("games.doom60d.wad", doom_wad_choice, -1);
CONFIG_INT("games.doom60d.debug", doom_debug_enabled, 0);

#define KEYQUEUE_SIZE 64

static volatile int module_running = 1;
static volatile int doom_running = 0;
static volatile int doom_task_active = 0;
static volatile uint32_t doom_start_ms = 0;
static volatile uint32_t doom_tick_count = 0;
static volatile uint32_t doom_draw_count = 0;
static volatile int zoom_run_pressed = 0;
static char doom_wad_files[DOOM_MAX_WAD_FILES][FIO_MAX_PATH_LENGTH];
static int doom_wad_file_count = 0;
static int doom_wad_scan_done = 0;
static char doom_requested_wad_path[FIO_MAX_PATH_LENGTH];
static char doom_session_wad_path[FIO_MAX_PATH_LENGTH];

static unsigned short key_queue[KEYQUEUE_SIZE];
static unsigned int key_write = 0;
static unsigned int key_read = 0;
static unsigned char key_state[256];
static uint32_t cheat_trash_first_ms;
static unsigned int cheat_trash_count;

#define DOOM_RAW_TRACE_MAX 192

struct doom_raw_trace_entry
{
    uint32_t ms;
    uint32_t type;
    uint32_t param;
    uint32_t arg;
    uint32_t obj;
};

static struct doom_raw_trace_entry doom_raw_trace[DOOM_RAW_TRACE_MAX];
static unsigned int doom_raw_trace_count = 0;

static uint32_t saved_palette[256];
static int palette_saved = 0;

extern int menu_redraw_blocked;
extern volatile int doom_ml_exit_requested;
extern boolean menuactive;

/* --- Logging Infrastructure --- */

static void doom_log_write(const char *text, unsigned int length)
{
    FILE *file;
    if (!doom_debug_enabled) return;
    file = FIO_OpenFile(DOOM_LOG_FILE, O_RDWR | O_SYNC);
    if (!file) file = FIO_CreateFile(DOOM_LOG_FILE);
    if (!file) return;
    FIO_SeekSkipFile(file, 0, SEEK_END);
    FIO_WriteFile(file, text, length);
    FIO_CloseFile(file);
}

#define DOOM_LOG(text) doom_log_write((text), sizeof(text) - 1)

static void doom_log_checkpoint(const char *where)
{
    char buffer[192];
    int length = snprintf(
        buffer,
        sizeof(buffer),
        "%s tick=%d draw=%d module=%d running=%d ms=%d\n",
        where, (unsigned int)doom_tick_count, (unsigned int)doom_draw_count,
        (int)module_running, (int)doom_running, (unsigned int)get_ms_clock()
    );
    if (length > 0) {
        unsigned int write_length = length < (int)sizeof(buffer) ? (unsigned int)length : (unsigned int)sizeof(buffer) - 1;
        doom_log_write(buffer, write_length);
    }
}

static void doom_log_reset(void)
{
    FILE *file;
    if (!doom_debug_enabled) return;
    file = FIO_CreateFile(DOOM_LOG_FILE);
    if (!file) return;
    static const char header[] = "DOOM60D engine log\n====================\n";
    FIO_WriteFile(file, header, sizeof(header) - 1);
    FIO_CloseFile(file);
}

/* --- Color and Palette Management --- */

static int clamp_int(int value, int low, int high)
{
    if (value < low) return low;
    if (value > high) return high;
    return value;
}

static uint32_t rgb_to_canon_yuv(unsigned int red, unsigned int green, unsigned int blue)
{
    int y = (77 * (int)red + 150 * (int)green + 29 * (int)blue) >> 8;
    int u = (-43 * (int)red - 85 * (int)green + 128 * (int)blue) >> 8;
    int v = (128 * (int)red - 107 * (int)green - 21 * (int)blue) >> 8;
    y = clamp_int(y, 0, 255); u = clamp_int(u, -128, 127); v = clamp_int(v, -128, 127);
    return (3u << 24) | ((uint32_t)(y & 0xff) << 16) | ((uint32_t)(u & 0xff) << 8) | ((uint32_t)(v & 0xff));
}

static void save_current_palette(void)
{
    if (palette_saved) return;
    for (int i = 0; i < 256; i++) saved_palette[i] = LCD_Palette[i * 3 + 2];
    palette_saved = 1;
}

static void install_doom_palette(void)
{
    save_current_palette();
    for (int i = 0; i < 256; i++) {
        uint32_t entry = rgb_to_canon_yuv(colors[i].r, colors[i].g, colors[i].b);
        EngDrvOut(LCD_Palette[i * 3], entry);
        EngDrvOut(LCD_Palette[i * 3 + 0x300], entry);
    }
    palette_changed = false;
}

static void restore_saved_palette(void)
{
    if (!palette_saved) return;
    for (int i = 0; i < 256; i++) {
        EngDrvOut(LCD_Palette[i * 3], saved_palette[i]);
        EngDrvOut(LCD_Palette[i * 3 + 0x300], saved_palette[i]);
    }
    palette_saved = 0;
}

static void clear_doom_area(void)
{
    uint8_t *vram = bmp_vram();
    if (!vram) return;
    for (int y = 0; y < DOOM_H; y++) {
        uint8_t *row = vram + (DOOM_Y + y) * BMPPITCH + DOOM_X;
        memset(row, COLOR_TRANSPARENT_GRAY, DOOM_W);
    }
}

/* --- Input Logic --- */

static uint32_t pulse_deadline[256];

static void queue_key(int pressed, unsigned char key)
{
    unsigned int next;
    pressed = pressed ? 1 : 0;
    if (key_state[key] == pressed) return;
    next = (key_write + 1) % KEYQUEUE_SIZE;
    if (next == key_read) {
        if (pressed) return;
        key_read = (key_read + 1) % KEYQUEUE_SIZE;
    }
    key_state[key] = pressed;
    key_queue[key_write] = ((pressed ? 1 : 0) << 8) | key;
    key_write = next;
}

static void tap_key(unsigned char key) { queue_key(1, key); queue_key(0, key); }
static void pulse_key(unsigned char key, uint32_t duration_ms) {
    queue_key(1, key);
    pulse_deadline[key] = (uint32_t)get_ms_clock() + duration_ms;
}
static void release_key(unsigned char key) { pulse_deadline[key] = 0; queue_key(0, key); }

static void release_direction_keys(void) {
    release_key(KEY_UPARROW); release_key(KEY_DOWNARROW);
    release_key(KEY_LEFTARROW); release_key(KEY_RIGHTARROW);
}

static void release_game_keys(void) {
    release_direction_keys();
    release_key(KEY_STRAFE_L); release_key(KEY_STRAFE_R);
    release_key(KEY_RALT); release_key(KEY_RSHIFT);
    release_key(KEY_FIRE); release_key(KEY_USE);
}

static void update_pulsed_keys(void) {
    static const unsigned char pulsed_keys[] = { KEY_UPARROW, KEY_DOWNARROW, KEY_LEFTARROW, KEY_RIGHTARROW, KEY_FIRE, KEY_USE, KEY_ESCAPE, KEY_ENTER, KEY_TAB, 'y' };
    uint32_t now = (uint32_t)get_ms_clock();
    for (unsigned int i = 0; i < COUNT(pulsed_keys); i++) {
        unsigned char key = pulsed_keys[i];
        uint32_t deadline = pulse_deadline[key];
        if (deadline && (int32_t)(now - deadline) >= 0) release_key(key);
    }
}

/* --- DOOMGeneric Port Hooks --- */

void DG_Init(void) { save_current_palette(); DOOM_LOG("DG_Init complete\n"); }

void DG_DrawFrame(void) {
    uint8_t *vram = bmp_vram();
    doom_draw_count++;
    if (!vram || !DG_ScreenBuffer) return;
    if (palette_changed) install_doom_palette();
    for (int y = 0; y < DOOM_H; y++) {
        uint8_t *dst = vram + (DOOM_Y + y) * BMPPITCH + DOOM_X;
        uint8_t *src = (uint8_t *)DG_ScreenBuffer + y * DOOM_W;
        memcpy(dst, src, DOOM_W);
    }
}

void DG_SleepMs(uint32_t ms) { msleep(ms); }
uint32_t DG_GetTicksMs(void) { return (uint32_t)get_ms_clock(); }

int DG_GetKey(int *pressed, unsigned char *doom_key) {
    update_pulsed_keys();
    if (key_read == key_write) return 0;
    unsigned short event = key_queue[key_read];
    key_read = (key_read + 1) % KEYQUEUE_SIZE;
    *pressed = (event >> 8) & 1;
    *doom_key = event & 0xff;
    return 1;
}

void DG_SetWindowTitle(const char *title) {}

/* --- Weapon Selection Cycle --- */

static void cycle_owned_weapon(int direction) {
    player_t *player;
    int start;
    if (menuactive) return;
    player = &players[consoleplayer];
    start = (player->pendingweapon != wp_nochange) ? (int)player->pendingweapon : (int)player->readyweapon;
    for (int step = 1; step < NUMWEAPONS; step++) {
        int candidate = (start + direction * step + NUMWEAPONS) % NUMWEAPONS;
        if (player->weaponowned[candidate]) {
            player->pendingweapon = (weapontype_t)candidate;
            return;
        }
    }
}

/* --- WAD File Scanner Logic --- */

static int wad_exists(const char *path) {
    FILE *file = FIO_OpenFile(path, O_RDONLY | O_SYNC);
    if (!file) return 0;
    FIO_CloseFile(file);
    return 1;
}

static int ascii_lower(int character) { return character >= 'A' && character <= 'Z' ? character + ('a' - 'A') : character; }

static int has_wad_extension(const char *name) {
    size_t length = strlen(name);
    return length > 4 && name[length - 4] == '.' && ascii_lower(name[length - 3]) == 'w' && ascii_lower(name[length - 2]) == 'a' && ascii_lower(name[length - 1]) == 'd';
}

static int has_iwad_header(const char *path) {
    char header[4];
    FILE *file = FIO_OpenFile(path, O_RDONLY | O_SYNC);
    if (!file) return 0;
    int read = FIO_ReadFile(file, header, 4);
    FIO_CloseFile(file);
    return read == 4 && !memcmp(header, "IWAD", 4);
}

static void scan_wad_files(void) {
    struct fio_file *file; struct fio_dirent *dirent;
    doom_wad_file_count = 0;
    file = alloc_fio_file();
    if (!file) { doom_wad_scan_done = 1; return; }
    dirent = FIO_FindFirstEx(DOOM_WAD_DIR, file);
    if (!IS_ERROR(dirent)) {
        do {
            struct file_info info = convert_fio_file_info(file);
            char path[FIO_MAX_PATH_LENGTH];
            if (!info.name[0] || (info.mode & ATTR_DIRECTORY) || !has_wad_extension(info.name)) continue;
            snprintf(path, sizeof(path), "%s%s", DOOM_WAD_DIR, info.name);
            if (!has_iwad_header(path)) continue;
            snprintf(doom_wad_files[doom_wad_file_count], FIO_MAX_PATH_LENGTH, "%s", info.name);
            doom_wad_file_count++;
        } while (doom_wad_file_count < DOOM_MAX_WAD_FILES && FIO_FindNextEx(dirent, file) == 0);
        FIO_FindClose(dirent);
    }
    free(file);
    doom_wad_scan_done = 1;
    if (doom_wad_choice < 0 && doom_wad_file_count > 0) doom_wad_choice = 0;
}

/* --- Storage and Save Management --- */

static void ensure_doom_directories(void) {
    FIO_CreateDirectory("ML/DOOM");
    FIO_CreateDirectory(DOOM_SAVE_DIR);
    FIO_CreateDirectory(DOOM_CONFIG_DIR);
}

static int verify_save_storage(void) {
    const char *test_path = P_TempSaveGameFile();
    FILE *file = FIO_CreateFile(test_path);
    if (!file) return 0;
    FIO_CloseFile(file);
    FIO_RemoveFile(test_path);
    return 1;
}

/* --- The Main Doom Task --- */

static void doom60d_task(void *arg) {
    doom_log_reset();
    if (!doom_requested_wad_path[0]) {
        doom_running = 0; doom_task_active = 0; return;
    }
    snprintf(doom_session_wad_path, FIO_MAX_PATH_LENGTH, "%s", doom_requested_wad_path);
    P_SetSaveGameDir(doom_requested_wad_path);
    if (!verify_save_storage()) { doom_running = 0; doom_task_active = 0; return; }

    clrscr();
    menu_redraw_blocked = 1;
    doom_running = 1;
    DG_ResetInput();
    doom_cheat_menu_reset();

    char *argv[] = { "doom", "-iwad", doom_requested_wad_path, 0 };
    doom_ml_exit_requested = 0;
    doomgeneric_Create(3, argv);

    while (module_running && doom_running && !ml_shutdown_requested && !doom_ml_exit_requested) {
        doom_tick_count++;
        doomgeneric_Tick();
    }

    M_SaveDefaults();
    release_game_keys();
    clear_doom_area();
    restore_saved_palette();
    clrscr();
    doom_running = 0;
    doom_task_active = 0;
    menu_redraw_blocked = 0;
}

/* --- Menu System --- */

static MENU_SELECT_FUNC(doom60d_start) {
    if (doom_task_active) return;
    scan_wad_files();
    if (doom_wad_choice >= 0 && doom_wad_choice < doom_wad_file_count) {
        snprintf(doom_requested_wad_path, FIO_MAX_PATH_LENGTH, "%s%s", DOOM_WAD_DIR, doom_wad_files[doom_wad_choice]);
        doom_task_active = 1;
        task_create("doom_task", 0x1c, 0x10000, doom60d_task, (void *)0);
    }
}

static MENU_UPDATE_FUNC(doom_wad_update) {
    if (!doom_wad_scan_done) scan_wad_files();
    if (doom_wad_choice >= 0 && doom_wad_choice < doom_wad_file_count)
        MENU_SET_VALUE("%s", doom_wad_files[doom_wad_choice]);
    else
        MENU_SET_VALUE("No IWADs found");
}

static MENU_SELECT_FUNC(doom_wad_select) {
    if (!doom_wad_scan_done) scan_wad_files();
    if (doom_wad_file_count > 0) {
        doom_wad_choice = (doom_wad_choice + delta + doom_wad_file_count) % doom_wad_file_count;
    }
}

static struct menu_entry doom60d_menu[] = {
    {
        .name = "Doom",
        .select = doom60d_start,
        .help = "Launch Doom on EOS 60D",
        .children = (struct menu_entry[]) {
            { .name = "WAD", .priv = &doom_wad_choice, .select = doom_wad_select, .update = doom_wad_update, .help = "Choose WAD from ML/DOOM" },
            { .name = "Debug Logging", .priv = &doom_debug_enabled, .min = 0, .max = 1, .choices = (const char *[]) {"OFF", "ON"} },
            MENU_EOL
        }
    }
};

/* --- 60D Event Callback --- */

#define GMT_60D_UP 0x24
#define GMT_60D_DOWN 0x28
#define GMT_60D_LEFT 0x2a
#define GMT_60D_RIGHT 0x26
#define GMT_60D_UNPRESS_UDLR 0x2c
#define GMT_60D_SET 0x04
#define GMT_60D_SET_UP 0x05
#define GMT_60D_WHEEL_L 0x02
#define GMT_60D_WHEEL_R 0x03
#define GMT_60D_MENU 0x06
#define GMT_60D_INFO 0x07
#define GMT_60D_PLAY 0x0b
#define GMT_60D_TRASH 0x0c
#define GMT_60D_ZOOM_IN 0x0d
#define GMT_60D_ZOOM_IN_UP 0x0e

static unsigned int doom60d_keypress_raw(unsigned int context) {
    struct event *event = (struct event *)(uintptr_t)context;
    if (!doom_running || !event || event->type != 0) return 1;
    unsigned int key = event->param;

    if (doom_cheat_menu_captures_input()) {
        switch(key) {
            case GMT_60D_UP: doom_cheat_menu_queue(DOOM_CHEAT_MENU_UP); return 0;
            case GMT_60D_DOWN: doom_cheat_menu_queue(DOOM_CHEAT_MENU_DOWN); return 0;
            case GMT_60D_SET: doom_cheat_menu_queue(DOOM_CHEAT_MENU_SELECT); return 0;
            case GMT_60D_MENU: doom_cheat_menu_queue(DOOM_CHEAT_MENU_BACK); return 0;
            default: break;
        }
        return 0;
    }

    switch (key) {
        case GMT_60D_UP:    queue_key(1, KEY_UPARROW);    return 0;
        case GMT_60D_DOWN:  queue_key(1, KEY_DOWNARROW);  return 0;
        case GMT_60D_LEFT:  queue_key(1, KEY_LEFTARROW);  return 0;
        case GMT_60D_RIGHT: queue_key(1, KEY_RIGHTARROW); return 0;
        case GMT_60D_UNPRESS_UDLR: release_direction_keys(); return 0;
        case GMT_60D_SET:   queue_key(1, KEY_FIRE);       return 0;
        case GMT_60D_SET_UP: release_key(KEY_FIRE);       return 0;
        case GMT_60D_WHEEL_L: cycle_owned_weapon(-1);     return 0;
        case GMT_60D_WHEEL_R: cycle_owned_weapon(1);      return 0;
        case GMT_60D_INFO:  tap_key(KEY_TAB);             return 0;
        case GMT_60D_PLAY:  tap_key(KEY_USE);             return 0;
        case GMT_60D_MENU:  tap_key(KEY_ESCAPE);          return 0;
        case GMT_60D_ZOOM_IN: queue_key(1, KEY_RSHIFT);   return 0;
        case GMT_60D_ZOOM_IN_UP: release_key(KEY_RSHIFT); return 0;
        default: return 1;
    }
}

static unsigned int doom60d_init(void) {
    module_running = 1; doom_running = 0; doom_task_active = 0;
    ensure_doom_directories();
    menu_add("Games", doom60d_menu, 1);
    return 0;
}

static unsigned int doom60d_deinit(void) {
    module_running = 0;
    msleep(100);
    return 0;
}

MODULE_INFO_START()
    MODULE_INIT(doom60d_init)
    MODULE_DEINIT(doom60d_deinit)
MODULE_INFO_END()

MODULE_CBRS_START()
    MODULE_CBR(CBR_KEYPRESS_RAW, doom60d_keypress_raw, 0)
MODULE_CBRS_END()

MODULE_CONFIGS_START()
    MODULE_CONFIG(doom_wad_choice)
    MODULE_CONFIG(doom_debug_enabled)
MODULE_CONFIGS_END()