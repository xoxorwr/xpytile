# Introduction

A lightweight X11 tiling helper that manages only the windows it spawns

Unlike a full tiling WM, this fork of xpytile runs alongside your existing window manager (eg XFWM, Openbox) and takes care of a specific set of applications, leaving everything else untouched

# Dependencies

- Python 3.8+
- python-xlib

# Usage

`python xpytile.py "subl -n" "terminator"`


# ToDo

- further strip down the fork to only contain what's needed
- port to C
