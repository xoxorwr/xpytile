#!/usr/bin/env python
"""
X-tiling helper — manages only windows from processes it spawns.
Quits automatically when all managed windows are closed.
"""

import argparse
import datetime
from functools import lru_cache
import os
import subprocess
import sys
import time
import types
import Xlib.display, Xlib.XK, Xlib.error, Xlib.protocol
from collections import namedtuple, defaultdict

# ==============================================================================
# Configuration — edit these values directly
# ==============================================================================

# Tiler to use (1=masterAndStackVertically, 2=vertically,
#               3=masterAndStackHorizontally, 4=horizontally, 5=maximize)
DEFAULT_TILER = 3

# Minimum window width/height in pixels
MIN_SIZE = 50

# Step size in pixels for enlarge/shrink master hotkey
STEP_SIZE = 50

# Maximize the sole remaining window automatically
MAXIMIZE_WHEN_ONE_WINDOW_LEFT = True

# Skip fullscreened or maximized windows when tiling
IGNORE_FULLSCREENED_WINDOWS = False
IGNORE_MAXIMIZED_WINDOWS    = False

# Master window default fraction of the work area
DEFAULT_WIDTH_MASTER  = 0.5   # masterAndStackVertically
DEFAULT_HEIGHT_MASTER = 0.5   # masterAndStackHorizontally

# Maximum windows each tiler handles simultaneously
MAX_WINDOWS_MASTER_STACK_VERT  = 3
MAX_WINDOWS_MASTER_STACK_HORIZ = 3
MAX_WINDOWS_VERTICALLY         = 3
MAX_WINDOWS_HORIZONTALLY       = 3

# Move mouse cursor into the newly focused window when using focus hotkeys
MOVE_MOUSE_INTO_ACTIVE_WINDOW = True

# Window class names (WM_CLASS instance name) to never tile or resize.
IGNORE_WINDOWS = [
    'Wrapper-2.0',
    'Xfdesktop',
    'Xfwm4',
    'Exo-desktop-item-edit',
    'Nm-connection-editor',
    'Polkit-gnome-authentication-agent-1',
    'Ulauncher',
    'rofi',
]

# Hotkey modifier: 64=Super, 8=Alt, -1=any
HOTKEY_MODIFIER = 64

# Keycodes — run `xev` to find yours
HOTKEYS = {
    'toggleresize':                   24,   # Super+Q
    'toggletiling':                   25,   # Super+W
    'toggleresizeandtiling':          26,   # Super+E
    'togglemaximizewhenonewindowleft':27,   # Super+R
    'toggledecoration':               52,   # Super+Y/Z
    'cyclewindows':                   49,   # Super+^
    'cycletiler':                     54,   # Super+C
    'swapwindows':                    9,    # Super+Esc
    'storecurrentwindowslayout':      15,   # Super+6
    'recreatewindowslayout':          14,   # Super+5
    'tilemasterandstackvertically':   10,   # Super+1
    'tilevertically':                 11,   # Super+2
    'tilemasterandstackhorizontally': 12,   # Super+3
    'tilehorizontally':               13,   # Super+4
    'tilemaximize':                   19,   # Super+0
    'increasemaxnumwindows':          58,   # Super+M
    'decreasemaxnumwindows':          57,   # Super+N
    'exit':                           61,   # Super+-
    'logactivewindow':                60,   # Super+.
    'shrinkmaster':                   38,   # Super+A
    'enlargemaster':                  39,   # Super+S
    'focusleft':                      113,  # Super+Left
    'focusright':                     114,  # Super+Right
    'focusup':                        111,  # Super+Up
    'focusdown':                      116,  # Super+Down
    'focusprevious':                  56,   # Super+B
}

# ==============================================================================

EventGeometry = namedtuple('EventGeometry', ['x', 'y', 'width', 'height'])

# frameToClient: frame-window-id → client window-id
frameToClient: dict = {}

# windowsInfo: client-window-id → SimpleNamespace with per-window state
windowsInfo: dict = {}

# TI: global tiling state (replaces tilingInfo dict)
TI: types.SimpleNamespace = None  # populated by init_tiling_info()

# True once the first managed window has been seen; gates auto-quit on startup
_had_managed_windows: bool = False

# Echo-vs-drag detection: programmatic echoes and app-level grid-snaps are
# distinguished from genuine user WM-drags by querying the pointer button state
# inside the CONFIGURE_NOTIFY handler.  No bookkeeping set is needed: inline
# cache updates in resize_docked_windows ensure that neighbor CNs arriving while
# a drag is still in progress always have moved_border == 0 and are skipped
# before the pointer query is reached.


# ----------------------------------------------------------------------------------------------------------------------
# PID helpers
# ----------------------------------------------------------------------------------------------------------------------

def _proc_ppid(pid):
    try:
        with open(f'/proc/{pid}/status') as f:
            for line in f:
                if line.startswith('PPid:'):
                    return int(line.split()[1])
    except OSError:
        pass
    return None


def _proc_exe_name(pid):
    try:
        with open(f'/proc/{pid}/comm') as f:
            return f.read().strip()
    except OSError:
        return ''


def _find_pids_by_exe(name):
    """Scan /proc for live PIDs whose comm or argv[0] prefix-matches name (bidirectional)."""
    found = set()
    name_lower = name.lower()
    try:
        for entry in os.scandir('/proc'):
            if not entry.name.isdigit():
                continue
            pid = int(entry.name)
            try:
                candidates = set()
                comm = _proc_exe_name(pid)
                if comm:
                    candidates.add(comm.lower())
                with open(f'/proc/{pid}/cmdline', 'rb') as f:
                    raw = f.read().split(b'\x00')
                if raw and raw[0]:
                    argv0 = os.path.basename(raw[0].decode('utf-8', errors='replace'))
                    if argv0:
                        candidates.add(argv0.lower())
                for c in candidates:
                    if c.startswith(name_lower) or name_lower.startswith(c):
                        found.add(pid)
                        break
            except (ValueError, OSError):
                pass
    except OSError:
        pass
    return found


def pid_is_tracked(win_pid, tracked_pids):
    current = win_pid
    for _ in range(64):
        if current is None or current <= 1:
            break
        if current in tracked_pids:
            return True
        current = _proc_ppid(current)
    return False


# ----------------------------------------------------------------------------------------------------------------------
# Tiling logic
# ----------------------------------------------------------------------------------------------------------------------

def change_num_max_windows_by(delta):
    cd = Xroot.get_full_property(NET_CURRENT_DESKTOP, ANY_PROPERTYTYPE).value[0]
    t  = TI.tiler[cd]
    if   t == 1: TI.maxWin_masterVertic  = min(max(TI.maxWin_masterVertic  + delta, 2), 9)
    elif t == 2: TI.maxWin_vertically    = min(max(TI.maxWin_vertically    + delta, 2), 9)
    elif t == 3: TI.maxWin_masterHoriz   = min(max(TI.maxWin_masterHoriz   + delta, 2), 9)
    elif t == 4: TI.maxWin_horizontally  = min(max(TI.maxWin_horizontally  + delta, 2), 9)


def cycle_windows():
    cd    = Xroot.get_full_property(NET_CURRENT_DESKTOP, ANY_PROPERTYTYPE).value[0]
    winIDs = get_windows_on_desktop(cd)
    if len(winIDs) < 2:
        return
    for i, wid in enumerate(winIDs):
        nxt = winIDs[(i + 1) % len(winIDs)]
        n   = windowsInfo[nxt]
        set_window_position(wid, x=n.x, y=n.y)
        set_window_size(wid, width=n.width, height=n.height)
    disp.sync()
    update_windows_info()


def swap_windows(winID):
    cd    = Xroot.get_full_property(NET_CURRENT_DESKTOP, ANY_PROPERTYTYPE).value[0]
    winIDs = get_windows_on_desktop(cd)
    if len(winIDs) < 2:
        return
    winIDs = sorted(winIDs, key=lambda w: (windowsInfo[w].y, windowsInfo[w].x))
    if winID == winIDs[0]:
        return
    try:
        w0, w1 = windowsInfo[winIDs[0]], windowsInfo[winID]
        set_window_position(winID,     x=w0.x, y=w0.y)
        set_window_size(winID,         width=w0.width, height=w0.height)
        set_window_position(winIDs[0], x=w1.x, y=w1.y)
        set_window_size(winIDs[0],     width=w1.width, height=w1.height)
        disp.sync()
    except Exception:
        pass


def tile_windows(window_active, manuallyTriggered=False, tilerNumber=None,
                 desktopList=None, resizeMaster=0):
    if desktopList is None:
        cd = Xroot.get_full_property(NET_CURRENT_DESKTOP, ANY_PROPERTYTYPE).value[0]
        desktopList = [cd]
    for desktop in desktopList:
        if not manuallyTriggered and not TI.tileWindows[desktop]:
            continue
        if manuallyTriggered:
            if tilerNumber == 'next':
                TI.tiler[desktop] = [2, 3, 4, 5, 1][TI.tiler[desktop] - 1]
            elif tilerNumber is not None:
                TI.tiler[desktop] = tilerNumber
        if resizeMaster != 0 and TI.tiler[desktop] not in [1, 3]:
            continue
        t = TI.tiler[desktop]
        if   t == 1: tile_windows_master_and_stack_vertically(desktop, resizeMaster)
        elif t == 2: tile_windows_vertically(desktop)
        elif t == 3: tile_windows_master_and_stack_horizontally(desktop, resizeMaster)
        elif t == 4: tile_windows_horizontally(desktop)
        elif t == 5: tile_windows_maximize(desktop, window_active)


def _workarea():
    return Xroot.get_full_property(NET_WORKAREA, 0).value.tolist()[:4]


def _single_window(winID, desktop):
    set_window_decoration(winID, TI.windowDecoration[desktop])
    if TI.maximizeWhenOneWindowLeft[desktop]:
        x0, y0, w, h = _workarea()
        set_window_position(winID, x=x0, y=y0)
        set_window_size(winID, width=w, height=h)
        disp.sync()


def tile_windows_vertically(desktop):
    winIDs = get_windows_on_desktop(desktop)
    if not winIDs: return
    if len(winIDs) == 1: _single_window(winIDs[0], desktop); return
    x0, y0, W, H = _workarea()
    winIDs = sorted(winIDs, key=lambda w: windowsInfo[w].y)
    N = min(TI.maxWin_vertically, len(winIDs))
    y = y0; h = int(H / N)
    for i, wid in enumerate(winIDs[:N]):
        if i == N - 1: h = H + y0 - y + 1
        unmaximize_window(windowsInfo[wid].win)
        set_window_decoration(wid, TI.windowDecoration[desktop])
        set_window_position(wid, x=x0, y=y)
        set_window_size(wid, width=W, height=h)
        y += h
    for wid in winIDs[N:]: set_window_decoration(wid, True)
    disp.sync()
    update_windows_info()


def tile_windows_horizontally(desktop):
    winIDs = get_windows_on_desktop(desktop)
    if not winIDs: return
    if len(winIDs) == 1: _single_window(winIDs[0], desktop); return
    x0, y0, W, H = _workarea()
    winIDs = sorted(winIDs, key=lambda w: windowsInfo[w].x)
    N  = min(TI.maxWin_horizontally, len(winIDs))
    wi = windowsInfo[winIDs[0]]
    set_window_decoration(winIDs[0], TI.windowDecoration[desktop])
    if (wi.x == x0 and wi.y == y0 and wi.y2 - y0 == H - 1 and
            TI.minSize < wi.x2 - x0 < W - (N - 1) * TI.minSize):
        set_window_position(winIDs[0], x=x0, y=y0)
        I = 1; x = wi.x2 + 1; w = int((W - x) / (N - 1))
    else:
        I = 0; x = x0; w = int(W / N)
    for i, wid in enumerate(winIDs[I:N]):
        if i == N - 1: w = W + x0 - x + 1
        unmaximize_window(windowsInfo[wid].win)
        set_window_decoration(wid, TI.windowDecoration[desktop])
        set_window_position(wid, x=x, y=y0)
        set_window_size(wid, width=w, height=H + 1)
        x += w
    for wid in winIDs[N:]: set_window_decoration(wid, True)
    disp.sync()
    update_windows_info()


def tile_windows_master_and_stack_vertically(desktop, resizeMaster=0):
    winIDs = get_windows_on_desktop(desktop)
    if not winIDs: return
    if len(winIDs) == 1: _single_window(winIDs[0], desktop); return
    x0, y0, W, H = _workarea()
    winIDs = sorted(winIDs, key=lambda w: (windowsInfo[w].x, windowsInfo[w].y))
    wi     = windowsInfo[winIDs[0]]
    set_window_decoration(winIDs[0], TI.windowDecoration[desktop])
    if (wi.x == x0 and wi.y == y0 and wi.y2 - y0 == H - 1 and
            TI.minSize < wi.x2 - x0 < W - TI.minSize):
        set_window_position(winIDs[0], x=x0, y=y0)
        width = wi.width
        if resizeMaster != 0:
            width = min(max(width + resizeMaster, TI.minSize + 2), W - TI.minSize)
            set_window_size(winIDs[0], width=width, height=H)
            resize_docked_windows(winIDs[0], wi.win, 4, EventGeometry(x0, y0, width, H))
            disp.sync(); return
    else:
        unmaximize_window(wi.win)
        width = int(W * TI.defaultWidthMaster) + resizeMaster
        set_window_position(winIDs[0], x=x0, y=y0)
        set_window_size(winIDs[0], width=width, height=H)
    N = min(TI.maxWin_masterVertic - 1, len(winIDs) - 1)
    x = width + x0; y = y0; w = W - width; h = int(H / N)
    for i, wid in enumerate(winIDs[1:N + 1]):
        if i == N - 1: h = H + y0 - y + 1
        unmaximize_window(windowsInfo[wid].win)
        set_window_decoration(wid, TI.windowDecoration[desktop])
        set_window_position(wid, x=x, y=y)
        set_window_size(wid, width=w, height=h)
        y += h
    for wid in winIDs[N + 1:]: set_window_decoration(wid, True)
    disp.sync()
    update_windows_info()


def tile_windows_master_and_stack_horizontally(desktop, resizeMaster=0):
    winIDs = get_windows_on_desktop(desktop)
    if not winIDs: return
    if len(winIDs) == 1: _single_window(winIDs[0], desktop); return
    x0, y0, W, H = _workarea()
    winIDs = sorted(winIDs, key=lambda w: (windowsInfo[w].y, windowsInfo[w].x))
    wi     = windowsInfo[winIDs[0]]
    set_window_decoration(winIDs[0], TI.windowDecoration[desktop])
    if (wi.x == x0 and wi.y == y0 and wi.x2 - x0 == W - 1 and
            TI.minSize < wi.y2 - y0 < H - TI.minSize):
        set_window_position(winIDs[0], x=x0, y=y0)
        height = wi.height
        if resizeMaster != 0:
            height = min(max(height + resizeMaster, TI.minSize + 2), H - TI.minSize)
            set_window_size(winIDs[0], width=W, height=height)
            resize_docked_windows(winIDs[0], wi.win, 8, EventGeometry(x0, y0, W, height))
            disp.sync(); return
    else:
        unmaximize_window(wi.win)
        height = int(H * TI.defaultHeightMaster)
        set_window_position(winIDs[0], x=x0, y=y0)
        set_window_size(winIDs[0], width=W, height=height)
    N = min(TI.maxWin_masterHoriz - 1, len(winIDs) - 1)
    x = x0; y = height + y0; h = H - height; w = int(W / N)
    for i, wid in enumerate(winIDs[1:N + 1]):
        if i == N - 1: w = W + x0 - x + 1
        unmaximize_window(windowsInfo[wid].win)
        set_window_decoration(wid, TI.windowDecoration[desktop])
        set_window_position(wid, x=x, y=y)
        set_window_size(wid, width=w, height=h)
        x += w
    for wid in winIDs[N + 1:]: set_window_decoration(wid, True)
    disp.sync()
    update_windows_info()


def tile_windows_maximize(desktop, window_active, winID=None):
    x0, y0, W, H = _workarea()
    if winID is None:
        winID = Xroot.get_full_property(NET_ACTIVE_WINDOW, ANY_PROPERTYTYPE).value[0]
    set_window_decoration(winID, TI.windowDecoration[desktop])
    set_window_position(winID, x=x0, y=y0)
    set_window_size(winID, width=W, height=H)
    mask = Xlib.X.SubstructureRedirectMask | Xlib.X.SubstructureNotifyMask
    for atom in [NET_WM_STATE_MAXIMIZED_VERT, NET_WM_STATE_MAXIMIZED_HORZ]:
        Xroot.send_event(Xlib.protocol.event.ClientMessage(
            window=window_active, client_type=NET_WM_STATE,
            data=(32, [1, atom, 0, 1, 0])), event_mask=mask)
    disp.flush()


# ----------------------------------------------------------------------------------------------------------------------
# Window geometry / focus helpers
# ----------------------------------------------------------------------------------------------------------------------

def get_parent_window(window):
    try:
        p = window; parent = p
        while p.id != Xroot.id:
            parent = p
            p = p.query_tree().parent
        return parent
    except Exception:
        return None


def get_window_geometry(win, winID=None):
    try:
        wi = windowsInfo.get(winID) if winID is not None else None
        if wi is not None and wi.winParent is not None:
            return wi.winParent.get_geometry()
        return get_parent_window(win).get_geometry()
    except Exception:
        return None


def get_windows_name(winID, window):
    wi = windowsInfo.get(winID)
    if wi:
        return wi.name
    try:
        _, name = window.get_wm_class()
        return name
    except Exception:
        return 'UNKNOWN'


@lru_cache
def get_windows_title(window):
    try:
        title = window.get_full_property(NET_WM_NAME, 0).value
        return title.decode('UTF8', 'replace') if isinstance(title, bytes) else title
    except Exception:
        return '<unnamed?>'


def get_windows_on_desktop(desktop):
    result = []
    for winID, wi in windowsInfo.items():
        try:
            if wi.desktop == desktop:
                props = wi.win.get_full_property(NET_WM_STATE, 0).value.tolist()
                if (NET_WM_STATE_STICKY not in props and NET_WM_STATE_HIDDEN not in props and
                        (not TI.ignoreMaximizedWindows or not is_window_maximized(winID))):
                    result.append(winID)
        except (Xlib.error.BadWindow, AttributeError):
            pass
    return result


def is_window_fullscreened(winID):
    try:
        win = windowsInfo[winID].win if winID in windowsInfo \
              else disp.create_resource_object('window', winID)
        return NET_WM_STATE_FULLSCREEN in win.get_full_property(NET_WM_STATE, 0).value.tolist()
    except Exception:
        return False


def is_window_maximized(winID):
    try:
        win = windowsInfo[winID].win if winID in windowsInfo \
              else disp.create_resource_object('window', winID)
        states = win.get_full_property(NET_WM_STATE, 0).value.tolist()
        return NET_WM_STATE_MAXIMIZED_HORZ in states and NET_WM_STATE_MAXIMIZED_VERT in states
    except Exception:
        return False


def unmaximize_window(window):
    mask = Xlib.X.SubstructureRedirectMask | Xlib.X.SubstructureNotifyMask
    for atom in [NET_WM_STATE_MAXIMIZED_VERT, NET_WM_STATE_MAXIMIZED_HORZ]:
        Xroot.send_event(Xlib.protocol.event.ClientMessage(
            window=window, client_type=NET_WM_STATE,
            data=(32, [0, atom, 0, 1, 0])), event_mask=mask)
    disp.flush()


def set_window_decoration(winID, status):
    try:
        window = windowsInfo[winID].win
        if window.get_property(GTK_FRAME_EXTENTS, ANY_PROPERTYTYPE, 0, 32) is not None:
            return
        result = window.get_property(MOTIF_WM_HINTS, ANY_PROPERTYTYPE, 0, 32)
        if result:
            hints = result.value
            if hints[2] == int(status): return
            hints[2] = int(status)
        else:
            hints = (2, 0, int(status), 0, 0)
        window.change_property(MOTIF_WM_HINTS, MOTIF_WM_HINTS, 32, hints)
        wi = windowsInfo[winID]
        set_window_position(winID, x=wi.x, y=wi.y)
        set_window_size(winID, width=wi.width, height=wi.height)
    except Exception:
        pass


def set_window_position(winID, **kwargs):
    wi = windowsInfo.get(winID)
    if wi is None: return
    try:
        window = wi.win
        if window.get_property(MOTIF_WM_HINTS, ANY_PROPERTYTYPE, 0, 32).value[2] == 0:
            window.configure(**kwargs)
        else:
            try:
                wi.winSetXY.configure(**kwargs)
            except (AttributeError, TypeError):
                set_setxy_win(winID)
                try:
                    wi.winSetXY.configure(**kwargs)
                except (AttributeError, TypeError):
                    pass
    except (Xlib.error.BadWindow, AttributeError, KeyError):
        pass


def set_window_size(winID, **kwargs):
    wi = windowsInfo.get(winID)
    if wi is None: return
    try:
        wi.winParent.configure(**kwargs)
    except AttributeError:
        pass


def set_setxy_win(winID):
    wi = windowsInfo.get(winID)
    if wi is None: return
    try:
        if wi.winSetXY is not None:
            return
        unmaximize_window(wi.win)
        oldX, oldY = wi.x, wi.y
        wi.winParent.configure(y=oldY + 1)
        disp.sync()
        time.sleep(0.05)
        newGeom = get_window_geometry(wi.winParent)
        wi.winSetXY = wi.winParent if abs(oldY + 1 - newGeom.y) <= 1 else wi.win
        wi.winSetXY.configure(x=oldX, y=oldY)
        disp.sync()
    except (Xlib.error.BadWindow, AttributeError):
        pass


def set_window_focus(windowID_active, window_active, direction='left'):
    wi_active = windowsInfo.get(windowID_active)
    if wi_active is None: return windowID_active, window_active
    winIDs = get_windows_on_desktop(wi_active.desktop)
    if len(winIDs) < 2: return windowID_active, window_active
    xa, ya = wi_active.x, wi_active.y
    best_d, winID_next = 1e99, None
    for wid in winIDs:
        if wid == windowID_active: continue
        wx, wy = windowsInfo[wid].x, windowsInfo[wid].y
        if   direction == 'up'    and ya >  wy: d = ya - wy + abs(wx - xa) / 2
        elif direction == 'down'  and ya <  wy: d = wy - ya + abs(wx - xa) / 2
        elif direction == 'right' and xa <  wx: d = wx - xa + abs(wy - ya) / 2
        elif direction == 'left'  and xa >  wx: d = xa - wx + abs(wy - ya) / 2
        else: continue
        if d < best_d: best_d, winID_next = d, wid
    if winID_next:
        wn = windowsInfo[winID_next]
        wn.win.set_input_focus(Xlib.X.RevertToParent, 0)
        wn.win.configure(stack_mode=Xlib.X.Above)
        if TI.moveMouseIntoActiveWindow:
            Xlib.ext.xtest.fake_input(disp, Xlib.X.MotionNotify,
                                      x=int((wn.x + wn.x2) / 2), y=int((wn.y + wn.y2) / 2))
            hightlight_mouse_cursor()
        wn.time = datetime.datetime.now()
        windowID_active = winID_next
        window_active   = disp.create_resource_object('window', winID_next)
    return windowID_active, window_active


def set_window_focus_to_previous(windowID_active, window_active):
    wi_active = windowsInfo.get(windowID_active)
    if wi_active is None: return windowID_active, window_active
    winIDs = get_windows_on_desktop(wi_active.desktop)
    if len(winIDs) < 2: return windowID_active, window_active
    best_t, winID_next = 0, None
    for wid in winIDs:
        if wid == windowID_active: continue
        t = getattr(windowsInfo[wid], 'time', 0)
        if t and t > best_t:
            best_t, winID_next = t, wid
    if winID_next:
        wn = windowsInfo[winID_next]
        wn.win.set_input_focus(Xlib.X.RevertToParent, 0)
        wn.win.configure(stack_mode=Xlib.X.Above)
        if TI.moveMouseIntoActiveWindow:
            Xlib.ext.xtest.fake_input(disp, Xlib.X.MotionNotify,
                                      x=int((wn.x + wn.x2) / 2), y=int((wn.y + wn.y2) / 2))
            hightlight_mouse_cursor()
        wn.time = datetime.datetime.now()
        windowID_active = winID_next
        window_active   = disp.create_resource_object('window', winID_next)
    return windowID_active, window_active


def hightlight_mouse_cursor():
    if not disp.has_extension('XFIXES') or disp.query_extension('XFIXES') is None:
        return
    disp.xfixes_query_version()
    for i in range(3):
        if i: time.sleep(0.05)
        Xroot.xfixes_hide_cursor(); disp.sync()
        time.sleep(0.05)
        Xroot.xfixes_show_cursor(); disp.sync()


# ----------------------------------------------------------------------------------------------------------------------
# Resize docked windows
# ----------------------------------------------------------------------------------------------------------------------

def resize_docked_windows(windowID_active, window_active, moved_border, ag):
    if not moved_border or not ag: return
    wia = windowsInfo.get(windowID_active)
    if not wia: return
    if not TI.resizeWindows[wia.desktop]: return

    desktop = wia.desktop
    for wid, wi in windowsInfo.items():
        if wid == windowID_active or wi.desktop != desktop: continue

        ox = max(wi.x, ag.x) < min(wi.x2, ag.x + ag.width)
        oy = max(wi.y, ag.y) < min(wi.y2, ag.y + ag.height)

        if (moved_border & 1) and oy:
            gap = abs(wi.x2 - wia.x)
            if verbosityLevel > 0: print(f'  LEFT gap={gap}')
            if gap < 20:
                nw = ag.x - wi.x
                if nw >= TI.minSize:
                    set_window_size(wid, width=nw)
                    wi.width = nw; wi.x2 = wi.x + nw - 1

        if (moved_border & 2) and ox:
            gap = abs(wi.y2 - wia.y)
            if verbosityLevel > 0: print(f'  TOP gap={gap}')
            if gap < 20:
                nh = ag.y - wi.y
                if nh >= TI.minSize:
                    set_window_size(wid, height=nh)
                    wi.height = nh; wi.y2 = wi.y + nh - 1

        if (moved_border & 4) and oy:
            gap = abs(wi.x - (wia.x + wia.width))
            if verbosityLevel > 0: print(f'  RIGHT gap={gap}')
            if gap < 20:
                nx = ag.x + ag.width
                nw = wi.x2 - nx + 1
                if nw >= TI.minSize:
                    set_window_position(wid, x=nx)
                    set_window_size(wid, width=nw)
                    wi.x = nx; wi.width = nw

        if (moved_border & 8) and ox:
            gap = abs(wi.y - (wia.y + wia.height))
            if verbosityLevel > 0: print(f'  BOTTOM gap={gap}')
            if gap < 20:
                ny = ag.y + ag.height
                nh = wi.y2 - ny + 1
                if nh >= TI.minSize:
                    set_window_position(wid, y=ny)
                    set_window_size(wid, height=nh)
                    wi.y = ny; wi.height = nh

    wia.x = ag.x; wia.y = ag.y; wia.width = ag.width; wia.height = ag.height
    wia.x2 = ag.x + ag.width - 1; wia.y2 = ag.y + ag.height - 1
    disp.sync()


# ----------------------------------------------------------------------------------------------------------------------
# Layout store / recreate
# ----------------------------------------------------------------------------------------------------------------------

def store_window_geometries():
    cd = Xroot.get_full_property(NET_CURRENT_DESKTOP, ANY_PROPERTYTYPE).value[0]
    TI.userDefinedGeom[cd] = {
        wid: (windowsInfo[wid].x, windowsInfo[wid].y,
              windowsInfo[wid].width, windowsInfo[wid].height)
        for wid in get_windows_on_desktop(cd)
    }


def recreate_window_geometries():
    cd = Xroot.get_full_property(NET_CURRENT_DESKTOP, ANY_PROPERTYTYPE).value[0]
    for wid in get_windows_on_desktop(cd):
        try:
            x, y, w, h = TI.userDefinedGeom[cd][wid]
            wi = windowsInfo[wid]
            unmaximize_window(wi.win)
            wi.win.set_input_focus(Xlib.X.RevertToParent, Xlib.X.CurrentTime)
            wi.win.configure(stack_mode=Xlib.X.Above)
            set_window_position(wid, x=x, y=y)
            set_window_size(wid, width=w, height=h)
            disp.sync()
        except KeyError:
            pass


def log_active_window(windowID_active, window_active):
    path = os.path.join('/tmp', f'xpytile_{os.environ["USER"]}.log')
    with open(path, 'a') as f:
        f.write(f'[{datetime.datetime.now():%x %X}]  name: {get_windows_name(windowID_active, window_active)},'
                f'  title: {get_windows_title(window_active)}\n')


# ----------------------------------------------------------------------------------------------------------------------
# Per-desktop toggles
# ----------------------------------------------------------------------------------------------------------------------

def toggle_resize():
    d = Xroot.get_full_property(NET_CURRENT_DESKTOP, ANY_PROPERTYTYPE).value[0]
    TI.resizeWindows[d] = not TI.resizeWindows[d]

def toggle_tiling():
    d = Xroot.get_full_property(NET_CURRENT_DESKTOP, ANY_PROPERTYTYPE).value[0]
    TI.tileWindows[d] = not TI.tileWindows[d]
    return TI.tileWindows[d]

def toggle_maximize_when_one_window():
    d = Xroot.get_full_property(NET_CURRENT_DESKTOP, ANY_PROPERTYTYPE).value[0]
    TI.maximizeWhenOneWindowLeft[d] = not TI.maximizeWhenOneWindowLeft[d]

def toggle_window_decoration():
    d = Xroot.get_full_property(NET_CURRENT_DESKTOP, ANY_PROPERTYTYPE).value[0]
    status = not TI.windowDecoration[d]
    TI.windowDecoration[d] = status
    update_windows_info()
    for wid, wi in windowsInfo.items():
        if wi.desktop == d:
            set_window_decoration(wid, status)
    disp.sync()
    update_windows_info()


# ----------------------------------------------------------------------------------------------------------------------
# Hotkey / remote dispatch
# ----------------------------------------------------------------------------------------------------------------------

def handle_key_event(keyCode, windowID_active, window_active):
    hk = HOTKEYS
    if   keyCode == hk.get('toggleresize'):                    toggle_resize()
    elif keyCode == hk.get('toggletiling'):
        if toggle_tiling(): update_windows_info(); tile_windows(window_active)
    elif keyCode == hk.get('toggleresizeandtiling'):
        toggle_resize()
        if toggle_tiling(): update_windows_info(); tile_windows(window_active)
    elif keyCode == hk.get('toggledecoration'):                toggle_window_decoration()
    elif keyCode == hk.get('enlargemaster'):                   tile_windows(window_active, resizeMaster= TI.stepSize)
    elif keyCode == hk.get('shrinkmaster'):                    tile_windows(window_active, resizeMaster=-TI.stepSize)
    elif keyCode == hk.get('togglemaximizewhenonewindowleft'): toggle_maximize_when_one_window()
    elif keyCode == hk.get('cyclewindows'):                    update_windows_info(); cycle_windows()
    elif keyCode == hk.get('cycletiler'):                      update_windows_info(); tile_windows(window_active, manuallyTriggered=True, tilerNumber='next')
    elif keyCode == hk.get('swapwindows'):                     update_windows_info(); swap_windows(windowID_active)
    elif keyCode == hk.get('tilemasterandstackvertically'):    update_windows_info(); tile_windows(window_active, manuallyTriggered=True, tilerNumber=1)
    elif keyCode == hk.get('tilevertically'):                  update_windows_info(); tile_windows(window_active, manuallyTriggered=True, tilerNumber=2)
    elif keyCode == hk.get('tilemasterandstackhorizontally'):  update_windows_info(); tile_windows(window_active, manuallyTriggered=True, tilerNumber=3)
    elif keyCode == hk.get('tilehorizontally'):                update_windows_info(); tile_windows(window_active, manuallyTriggered=True, tilerNumber=4)
    elif keyCode == hk.get('tilemaximize'):                    update_windows_info(); tile_windows(window_active, manuallyTriggered=True, tilerNumber=5)
    elif keyCode == hk.get('increasemaxnumwindows'):           change_num_max_windows_by(1);  update_windows_info(); tile_windows(window_active)
    elif keyCode == hk.get('decreasemaxnumwindows'):           change_num_max_windows_by(-1); update_windows_info(); tile_windows(window_active)
    elif keyCode == hk.get('recreatewindowslayout'):           recreate_window_geometries()
    elif keyCode == hk.get('storecurrentwindowslayout'):       update_windows_info(); store_window_geometries()
    elif keyCode == hk.get('logactivewindow'):                 log_active_window(windowID_active, window_active)
    elif keyCode == hk.get('focusup'):      windowID_active, window_active = set_window_focus(windowID_active, window_active, 'up')
    elif keyCode == hk.get('focusdown'):    windowID_active, window_active = set_window_focus(windowID_active, window_active, 'down')
    elif keyCode == hk.get('focusleft'):    windowID_active, window_active = set_window_focus(windowID_active, window_active, 'left')
    elif keyCode == hk.get('focusright'):   windowID_active, window_active = set_window_focus(windowID_active, window_active, 'right')
    elif keyCode == hk.get('focusprevious'):windowID_active, window_active = set_window_focus_to_previous(windowID_active, window_active)
    elif keyCode == hk.get('exit'):
        for wid in windowsInfo: set_window_decoration(wid, True)
        disp.sync()
        raise SystemExit('exit hotkey')
    return windowID_active, window_active


def handle_remote_control_event(event, windowID_active, window_active):
    cmdNum  = event._data['data'][1].tolist()[0]
    cmdList = ('toggleresize', 'toggletiling', 'toggleresizeandtiling', 'togglemaximizewhenonewindowleft',
               'toggledecoration', 'cyclewindows', 'cycletiler', 'swapwindows',
               'storecurrentwindowslayout', 'recreatewindowslayout',
               'tilemasterandstackvertically', 'tilevertically',
               'tilemasterandstackhorizontally', 'tilehorizontally',
               'tilemaximize', 'increasemaxnumwindows', 'decreasemaxnumwindows', 'exit',
               'logactivewindow', 'shrinkmaster', 'enlargemaster',
               'focusleft', 'focusright', 'focusup', 'focusdown', 'focusprevious')
    try:
        keyCode = HOTKEYS[cmdList[cmdNum]]
        windowID_active, window_active = handle_key_event(keyCode, windowID_active, window_active)
    except (IndexError, KeyError):
        pass
    return windowID_active, window_active


# ----------------------------------------------------------------------------------------------------------------------
# Window tracking
# ----------------------------------------------------------------------------------------------------------------------

def update_windows_info(windowID_active=None, only_geometries=False, update_geometries=True):
    global windowsInfo, frameToClient, _had_managed_windows

    if only_geometries:
        for wid, wi in windowsInfo.items():
            g = get_window_geometry(wi.win, wid)
            if g:
                wi.x = g.x; wi.y = g.y; wi.width = g.width; wi.height = g.height
                wi.x2 = g.x + g.width - 1; wi.y2 = g.y + g.height - 1
        return False, set()

    windowIDs         = Xroot.get_full_property(NET_CLIENT_LIST, ANY_PROPERTYTYPE).value
    numWindowsChanged = False
    desktopList       = []

    for wid in list(windowsInfo.keys()):
        if wid not in windowIDs:
            pw = windowsInfo[wid].winParent
            if pw and pw.id in frameToClient:
                del frameToClient[pw.id]
            del windowsInfo[wid]
            numWindowsChanged = True

    if TI.pids and _had_managed_windows and not windowsInfo:
        if verbosityLevel > 0: print('All managed windows closed — exiting.')
        raise SystemExit(0)

    for wid in windowIDs:
        try:
            if wid in windowsInfo:
                if update_geometries:
                    wi  = windowsInfo[wid]
                    win = wi.win
                    desktop = win.get_full_property(NET_WM_DESKTOP, ANY_PROPERTYTYPE).value[0]
                    g = get_window_geometry(win, wid)
                    if g is None: continue
                    if wi.desktop != desktop:
                        numWindowsChanged = True
                        desktopList += [desktop, wi.desktop]
                    wi.desktop = desktop
                    wi.x = g.x; wi.y = g.y; wi.width = g.width; wi.height = g.height
                    wi.x2 = g.x + g.width - 1; wi.y2 = g.y + g.height - 1
                continue

            win = disp.create_resource_object('window', wid)

            if TI.pids and wid in TI.pre_existing_window_ids:
                continue

            wm_state = win.get_full_property(NET_WM_STATE, 0).value.tolist()
            if NET_WM_STATE_MODAL  in wm_state: continue
            if NET_WM_STATE_STICKY in wm_state: continue

            try:
                wc   = win.get_wm_class()
                name = wc[1] if wc and len(wc) > 1 else ''
                if any(name.lower() == ign.lower() for ign in IGNORE_WINDOWS):
                    if verbosityLevel > 1: print(f'Skipping ignored: "{name}" id={wid}')
                    continue
            except Exception:
                name = ''

            if TI.pids:
                try:
                    pp = win.get_full_property(NET_WM_PID, 0)
                    if pp is not None and len(pp.value) > 0:
                        if not pid_is_tracked(int(pp.value[0]), TI.pids):
                            if verbosityLevel > 1: print(f'Skipping id={wid} (pid not tracked)')
                            continue
                except Exception:
                    pass

            desktop   = win.get_full_property(NET_WM_DESKTOP, ANY_PROPERTYTYPE).value[0]
            g         = get_window_geometry(win, wid)
            if g is None: continue
            parentWin = get_parent_window(win)

            wi = types.SimpleNamespace(
                name=name, win=win, winParent=parentWin, winSetXY=None,
                desktop=desktop, time=0,
                x=g.x, y=g.y, width=g.width, height=g.height,
                x2=g.x + g.width - 1, y2=g.y + g.height - 1,
            )
            windowsInfo[wid] = wi

            if parentWin:
                try:
                    parentWin.change_attributes(event_mask=Xlib.X.StructureNotifyMask)
                except Xlib.error.BadWindow:
                    pass
                frameToClient[parentWin.id] = wid

            numWindowsChanged = True
            _had_managed_windows = True
            if verbosityLevel > 0:
                print(f'Tracking: "{name}" id={wid} desktop={desktop}')

        except Exception:
            pass

    if windowID_active is not None:
        wi = windowsInfo.get(windowID_active)
        if wi: wi.time = time.time()

    return numWindowsChanged, set(desktopList)


# ----------------------------------------------------------------------------------------------------------------------
# Initialisation
# ----------------------------------------------------------------------------------------------------------------------

def init_tiling_info():
    global TI
    TI = types.SimpleNamespace(
        pids                      = set(),
        pre_existing_window_ids   = set(),
        resizeWindows             = defaultdict(lambda: True),
        tileWindows               = defaultdict(lambda: True),
        windowDecoration          = defaultdict(lambda: True),
        tiler                     = defaultdict(lambda: DEFAULT_TILER),
        maximizeWhenOneWindowLeft = defaultdict(lambda: MAXIMIZE_WHEN_ONE_WINDOW_LEFT),
        ignoreFullscreenedWindows = IGNORE_FULLSCREENED_WINDOWS,
        ignoreMaximizedWindows    = IGNORE_MAXIMIZED_WINDOWS,
        minSize                 = MIN_SIZE,
        stepSize                = STEP_SIZE,
        moveMouseIntoActiveWindow = MOVE_MOUSE_INTO_ACTIVE_WINDOW,
        defaultWidthMaster      = DEFAULT_WIDTH_MASTER,
        defaultHeightMaster     = DEFAULT_HEIGHT_MASTER,
        maxWin_masterVertic     = MAX_WINDOWS_MASTER_STACK_VERT,
        maxWin_masterHoriz      = MAX_WINDOWS_MASTER_STACK_HORIZ,
        maxWin_vertically       = MAX_WINDOWS_VERTICALLY,
        maxWin_horizontally     = MAX_WINDOWS_HORIZONTALLY,
        userDefinedGeom         = {},
    )


def init(extra_args=None):
    global disp, Xroot, screen, windowsInfo
    global NET_ACTIVE_WINDOW, NET_WM_DESKTOP, NET_CLIENT_LIST, NET_CURRENT_DESKTOP
    global NET_WM_STATE_FULLSCREEN, NET_WM_STATE_MAXIMIZED_VERT, NET_WM_STATE_MAXIMIZED_HORZ
    global NET_WM_STATE, NET_WM_STATE_HIDDEN, NET_WORKAREA, NET_WM_NAME, NET_WM_STATE_MODAL
    global NET_WM_STATE_STICKY, MOTIF_WM_HINTS, ANY_PROPERTYTYPE, GTK_FRAME_EXTENTS
    global XPYTILE_REMOTE, NET_WM_PID

    disp   = Xlib.display.Display()
    screen = disp.screen()
    Xroot  = screen.root

    NET_ACTIVE_WINDOW           = disp.get_atom('_NET_ACTIVE_WINDOW')
    NET_WM_DESKTOP              = disp.get_atom('_NET_WM_DESKTOP')
    NET_CLIENT_LIST             = disp.get_atom('_NET_CLIENT_LIST')
    NET_CURRENT_DESKTOP         = disp.get_atom('_NET_CURRENT_DESKTOP')
    NET_WM_STATE_FULLSCREEN     = disp.get_atom('_NET_WM_STATE_FULLSCREEN')
    NET_WM_STATE_MAXIMIZED_VERT = disp.get_atom('_NET_WM_STATE_MAXIMIZED_VERT')
    NET_WM_STATE_MAXIMIZED_HORZ = disp.get_atom('_NET_WM_STATE_MAXIMIZED_HORZ')
    NET_WM_STATE                = disp.get_atom('_NET_WM_STATE')
    NET_WM_STATE_HIDDEN         = disp.get_atom('_NET_WM_STATE_HIDDEN')
    NET_WM_NAME                 = disp.get_atom('_NET_WM_NAME')
    NET_WORKAREA                = disp.get_atom('_NET_WORKAREA')
    NET_WM_STATE_MODAL          = disp.get_atom('_NET_WM_STATE_MODAL')
    NET_WM_STATE_STICKY         = disp.get_atom('_NET_WM_STATE_STICKY')
    MOTIF_WM_HINTS              = disp.get_atom('_MOTIF_WM_HINTS')
    GTK_FRAME_EXTENTS           = disp.get_atom('_GTK_FRAME_EXTENTS')
    ANY_PROPERTYTYPE            = Xlib.X.AnyPropertyType
    XPYTILE_REMOTE              = disp.get_atom('_XPYTILE_REMOTE')
    NET_WM_PID                  = disp.intern_atom('_NET_WM_PID')

    init_tiling_info()

    modifier = HOTKEY_MODIFIER if HOTKEY_MODIFIER != -1 else Xlib.X.AnyModifier
    for keyCode in HOTKEYS.values():
        Xroot.grab_key(keyCode, modifier, 1, Xlib.X.GrabModeAsync, Xlib.X.GrabModeAsync)

    try:
        pre_existing = set(Xroot.get_full_property(NET_CLIENT_LIST, ANY_PROPERTYTYPE).value.tolist())
    except Exception:
        pre_existing = set()
    TI.pre_existing_window_ids = pre_existing
    if verbosityLevel > 0:
        print(f'Pre-existing windows (ignored): {pre_existing}')

    if extra_args:
        for cmd in extra_args:
            try:
                proc = subprocess.Popen(cmd.split())
                TI.pids.add(proc.pid)
                if verbosityLevel > 0: print(f"Spawned '{cmd}' PID={proc.pid}")
                time.sleep(0.4)
                if proc.poll() is not None:
                    exe_name  = os.path.basename(cmd.split()[0])
                    live_pids = _find_pids_by_exe(exe_name)
                    TI.pids.update(live_pids)
                    if verbosityLevel > 0:
                        print(f"  '{cmd}' exited quickly; tracking '{exe_name}': {live_pids}")
            except Exception as e:
                print(f"Error spawning '{cmd}': {e}")

    window_active        = disp.get_input_focus().focus
    windowID_active      = Xroot.get_full_property(NET_ACTIVE_WINDOW, ANY_PROPERTYTYPE).value[0]
    window_active_parent = get_parent_window(window_active)

    windowsInfo = {}
    update_windows_info(windowID_active)

    Xroot.change_attributes(event_mask=Xlib.X.PropertyChangeMask | Xlib.X.KeyReleaseMask)
    return window_active, window_active_parent, windowID_active


# ----------------------------------------------------------------------------------------------------------------------
# Main event loop
# ----------------------------------------------------------------------------------------------------------------------

def run(window_active, window_active_parent, windowID_active):
    PROPERTY_NOTIFY  = Xlib.X.PropertyNotify
    CONFIGURE_NOTIFY = Xlib.X.ConfigureNotify
    KEY_RELEASE      = Xlib.X.KeyRelease

    tile_windows(window_active)
    while True:
        event = disp.next_event()

        if event.type == Xlib.X.ClientMessage and event._data['client_type'] == XPYTILE_REMOTE:
            windowID_active, window_active = \
                handle_remote_control_event(event, windowID_active, window_active)

        elif event.type == PROPERTY_NOTIFY and event.atom in [NET_ACTIVE_WINDOW, NET_CURRENT_DESKTOP]:
            windowID_active      = Xroot.get_full_property(NET_ACTIVE_WINDOW, ANY_PROPERTYTYPE).value[0]
            window_active        = disp.create_resource_object('window', windowID_active)
            window_active_parent = get_parent_window(window_active)
            numWindowsChanged, desktopList = update_windows_info(windowID_active, update_geometries=False)

            if verbosityLevel > 0:
                label = 'Active window' if event.atom == NET_ACTIVE_WINDOW else 'Desktop'
                extra = ', windows changed' if numWindowsChanged else ''
                print(f'{label}: "{get_windows_name(windowID_active, window_active)}"{extra}')

            if desktopList:         tile_windows(window_active, False, None, desktopList)
            elif numWindowsChanged: tile_windows(window_active)
            else:
                try:
                    cd = Xroot.get_full_property(NET_CURRENT_DESKTOP, ANY_PROPERTYTYPE).value[0]
                    if TI.tiler[cd] == 5:
                        tile_windows(window_active, False, 0)
                except Exception:
                    pass

        elif event.type == PROPERTY_NOTIFY:
            numWindowsChanged, _ = update_windows_info(windowID_active, update_geometries=False)
            if numWindowsChanged:
                if verbosityLevel > 0: print('num. windows changed')
                tile_windows(window_active)

        elif event.type == CONFIGURE_NOTIFY:
            eid = frameToClient.get(event.window.id)
            if eid is None: continue
            wi = windowsInfo.get(eid)
            if wi is None: continue

            moved_border = 0
            if wi.x  != event.x:                     moved_border |= 1
            if wi.y  != event.y:                     moved_border |= 2
            if wi.x2 != event.x + event.width  - 1:  moved_border |= 4
            if wi.y2 != event.y + event.height - 1:  moved_border |= 8

            if not moved_border:
                # Geometry unchanged — only check for a window wandering off-screen.
                if eid == windowID_active:
                    ww, wh = Xroot.get_full_property(NET_WORKAREA, 0).value.tolist()[2:4]
                    if (event.x <= -20 or event.y <= -20 or
                            event.x + event.width > ww + 20 or event.y + event.height > wh + 20):
                        tile_windows(wi.win)
                        update_windows_info()
                continue

            # Distinguish a genuine user WM-drag from a programmatic echo.
            #
            # If a mouse button is currently held down the user is dragging a
            # window border and we must propagate the resize to adjacent windows.
            # If no button is held the geometry change is either:
            #   (a) a WM echo of one of our own configure() calls, or
            #   (b) an app-level grid-snap that occurred after our configure()
            #       (e.g. a terminal snapping to character-cell boundaries).
            # In both cases the right response is to silently update the cache
            # to the actual post-snap geometry and do nothing else.  This is
            # what killed every previous approach: they tried to predict and
            # count echoes, but snapping apps emit a *different* geometry than
            # the one we requested, defeating exact-match or counter strategies.
            #
            # Neighbor echoes during a live drag are already harmless: because
            # resize_docked_windows updates each neighbor's cache inline before
            # disp.sync(), the CN that arrives for the neighbor will compute
            # moved_border == 0 and be handled by the `continue` above — the
            # pointer query is never reached for those events.
            try:
                _BTN = Xlib.X.Button1Mask | Xlib.X.Button2Mask | Xlib.X.Button3Mask
                btn_held = bool(Xroot.query_pointer().mask & _BTN)
            except Exception:
                btn_held = True   # safest: treat unknown state as a drag

            if not btn_held:
                # Programmatic echo or app snap — absorb silently, but read
                # the LIVE geometry from X rather than trusting the event.
                #
                # The event may be a stale pre-tiling echo: e.g. the window
                # was 1996 px wide, we tiled it to 1000 px, update_windows_info()
                # cached 1000, but the old WM echo (1996) arrives afterward.
                # Using the event geometry would corrupt the gap check that
                # live drags depend on.  A fresh get_geometry() returns whatever
                # the server has actually settled on right now, which is always
                # correct regardless of echo ordering or app-level grid-snapping.
                g = get_window_geometry(wi.win, eid)
                if g is not None:
                    wi.x = g.x;  wi.y = g.y
                    wi.width = g.width;  wi.height = g.height
                    wi.x2 = g.x + g.width  - 1
                    wi.y2 = g.y + g.height - 1
                continue

            if verbosityLevel > 0:
                print(f'CONFIGURE_NOTIFY id={eid} border={moved_border:04b} '
                      f'({event.x},{event.y},{event.width},{event.height})')

            g = EventGeometry(event.x, event.y, event.width, event.height)
            resize_docked_windows(eid, wi.win, moved_border, g)

        elif event.type == KEY_RELEASE:
            windowID_active, window_active = \
                handle_key_event(event.detail, windowID_active, window_active)


# ----------------------------------------------------------------------------------------------------------------------

def write_crashlog():
    import traceback
    msg  = traceback.format_exception(*sys.exc_info())
    path = os.path.join('/tmp', f'xpytile_crash_{os.environ["USER"]}.log')
    with open(path, 'a') as f:
        f.write(f'[{datetime.datetime.now():%x %X}] {"".join(msg)}\n')


def main():
    global verbosityLevel

    parser = argparse.ArgumentParser(prog='xpytile.py',
        description='X tiling helper — manages only the windows it spawns.')
    parser.add_argument('-v',  '--verbose',  action='store_true',
                        help='Print tracking and resize events')
    parser.add_argument('-vv', '--verbose2', action='store_true',
                        help='Also print skipped-window decisions')
    parser.add_argument('extra_args', nargs='*',
                        help='Commands to spawn and manage, e.g. "subl -n" "terminator"')
    args = parser.parse_args()
    verbosityLevel = 2 if args.verbose2 else (1 if args.verbose else 0)

    try:
        window_active, window_active_parent, windowID_active = init(args.extra_args)
        run(window_active, window_active_parent, windowID_active)
    except KeyboardInterrupt:
        raise SystemExit('terminated by ctrl-c')
    except SystemExit:
        raise
    except Exception:
        write_crashlog()
        raise


if __name__ == '__main__':
    main()
