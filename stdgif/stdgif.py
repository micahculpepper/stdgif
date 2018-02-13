#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
  stdgif -- Standard output for gifs

  The clever algorithm (that I had nothing to do with) that shows
  amazing ansi renderings of images was ported from Stefan Haustein's
  TerminalImageViewer <https://github.com/stefanhaustein/TerminalImageViewer>

  Requirements: requests <http://docs.python-requests.org>,
                Pillow <https://python-pillow.org/>

  usage: stdgif [-h] [-w WIDTH] [-f] [-d DELAY] [-o OUTPUT] [-s SEPERATOR] img

  positional arguments:
    img                   File to show

  optional arguments:
    -h, --help            show this help message and exit
    -w WIDTH, --width WIDTH
                          Width of file to show
    -f, --forever         Loop forever
    -d DELAY, --delay DELAY
                          The delay between images that make up a gif
    -o OUTPUT, --output OUTPUT
                          Generated bash script path - suitable for sourcing
                          from your .bashrc
    -s SEPERATOR, --seperator SEPERATOR
                          Print the seperator between frames of a gif (this can
                          be useful if piping output into another file or
                          program)

  Copyright (c) 2016 Tyler Cipriani <tyler@tylercipriani.com>

  This program is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
"""

from __future__ import print_function

import argparse
from fractions import Fraction
import itertools
import math
import os
import subprocess
import sys
import time

try:
    # Python 3 feature
    from shutil import get_terminal_size
except ImportError:
    # Backported Python 2 version
    try:
        from backports.shutil_get_terminal_size import get_terminal_size
    except ImportError:
        get_terminal_size = None

import requests

from PIL import Image, ImageSequence

BITMAPS = {
    0x00000000: ' ',
    # Block graphics
    0x0000000f: u'\u2581',  # lower 1/8
    0x000000ff: u'\u2582',  # lower 1/4
    0x00000fff: u'\u2583',
    0x0000ffff: u'\u2584',  # lower 1/2
    0x000fffff: u'\u2585',
    0x00ffffff: u'\u2586',  # lower 3/4
    0x0fffffff: u'\u2587',
    0xeeeeeeee: u'\u258a',  # left 3/4
    0xcccccccc: u'\u258c',  # left 1/2
    0x88888888: u'\u258e',  # left 1/4
    0x0000cccc: u'\u2596',  # quadrant lower left
    0x00003333: u'\u2597',  # quadrant lower right
    0xcccc0000: u'\u2598',  # quadrant upper left
    0xcccc3333: u'\u259a',  # diagonal 1/2
    0x33330000: u'\u259d',  # quadrant upper right

    # Line drawing subset: no double lines, no complex light lines
    # Simple light lines duplicated because there is no center pixel int
    # the 4x8 matrix
    0x000ff000: u'\u2501',  # Heavy horizontal
    0x66666666: u'\u2503',  # Heavy vertical

    0x00077666: u'\u250f',  # Heavy down and right
    0x000ee666: u'\u2513',  # Heavy down and left
    0x66677000: u'\u2517',  # Heavy up and right
    0x666ee000: u'\u251b',  # Heavy up and left

    0x66677666: u'\u2523',  # Heavy vertical and right
    0x666ee666: u'\u252b',  # Heavy vertical and left
    0x000ff666: u'\u2533',  # Heavy down and horizontal
    0x666ff000: u'\u253b',  # Heavy up and horizontal
    0x666ff666: u'\u254b',  # Heavy cross

    0x000cc000: u'\u2578',  # Bold horizontal left
    # 0x00066000: u'\u2579',  # Bold horizontal up
    0x00033000: u'\u257a',  # Bold horizontal right
    # 0x00066000: u'\u257b',  # Bold horizontal down

    0x06600660: u'\u254f',  # Heavy double dash vertical

    0x000f0000: u'\u2500',  # Light horizontal
    0x0000f000: u'\u2500',
    # 0x44444444: u'\u2502',  # Light vertical
    # 0x22222222: u'\u2502',

    0x000e0000: u'\u2574',  # light left
    0x0000e000: u'\u2574',  # light left
    0x44440000: u'\u2575',  # light up
    0x22220000: u'\u2575',  # light up
    0x00030000: u'\u2576',  # light right
    0x00003000: u'\u2576',  # light right
    0x00004444: u'\u2575',  # light down
    0x00002222: u'\u2575',  # light down

    # Misc technical

    0x44444444: u'\u23a2',  # [ extension
    0x22222222: u'\u23a5',  # ] extension

    # 12345678
    0x0f000000: u'\u23ba',  # Horizontal scanline 1
    0x00f00000: u'\u23bb',  # Horizontal scanline 3
    0x00000f00: u'\u23bc',  # Horizontal scanline 7
    0x000000f0: u'\u23bd',  # Horizontal scanline 9

    # Geometrical shapes. Tricky because some of them are too wide.

    0x00066000: u'\u25aa',  # Black small square
}


def esc(*args):
    """Escape ansi codes."""
    return ''.join((
        '\x1b[',
        ';'.join(str(arg) for arg in args),
        'sm'
    ))


def clamp(val, small, large):
    """Clamp val to a range."""
    return min(max(int(val), small), large)


def rgb_to_tput(rgb):
    """Convert rgb string (like "0, 0, 0") into a list (like [0, 0, 0])."""
    return [clamp(c, 0, 255) for c in rgb.split(',')]


def make_char(c, fg, bg):
    """Return escaped ansi char."""
    if fg[0] == fg[1] == fg[2] == bg[0] == bg[1] == bg[2] == 0:
        return '\x1b[0m '

    return ''.join((
        esc(38, 2, fg[0], fg[1], fg[2]),
        esc(48, 2, bg[0], bg[1], bg[2]),
        c.encode('utf-8')
    ))


def make_percent(num, den):
    """Make a numerator and a denominator into a percentage."""
    return math.floor(100.0 * (float(num) / max(den, 1)))


def handle_pixel(img, x, y):
    """Turn a 4x8 dict of rgb tuples into a single-ansi char."""
    w, h = img.size
    x_offset = min(x + 4, w)
    y_offset = min(y + 8, h)

    max_rgb = [0, 0, 0]
    min_rgb = [255, 255, 255]

    for i in range(x, x_offset):
        for j in range(y, y_offset):
            rgba = img.getpixel((i, j))
            for channel in range(0, 3):
                max_rgb[channel] = max(max_rgb[channel], rgba[channel])
                min_rgb[channel] = min(min_rgb[channel], rgba[channel])

    split_channel = 0
    best_split = 0

    for channel in range(0, 3):
        split = max_rgb[channel] - min_rgb[channel]

        if split > best_split:
            best_split = split
            split_channel = channel

    split_val = min_rgb[split_channel] + best_split / 2

    bits = 0
    bg_color = []
    fg_color = []

    for j in range(y, y_offset):
        for i in range(x, x_offset):
            rgba = img.getpixel((i, j))
            r, g, b, _ = rgba
            bits = bits << 1
            index = rgba[split_channel]
            num = (index & 255)
            if int(num) > split_val:
                bits |= 1
                fg_color.append((r, g, b))
            else:
                bg_color.append((r, g, b))

    avg_bg_rgb = [sum(color) / len(color) for color in zip(*bg_color)]
    avg_fg_rgb = [sum(color) / len(color) for color in zip(*fg_color)]

    if not avg_fg_rgb:
        avg_fg_rgb = [0, 0, 0]

    if not avg_bg_rgb:
        avg_fg_rgb = [0, 0, 0]

    best_diff = sys.maxint
    inverted = False
    for bitmap in list(BITMAPS.keys()):
        xor = bin(bitmap ^ bits)
        diff = xor.count('1')
        if diff < best_diff:
            character = BITMAPS[bitmap]
            best_diff = diff
            inverted = False

        # make sure to & the ~ with 0xffffffff to fill up all 32 bits
        not_xor = bin((~bitmap & 0xffffffff) ^ bits)
        diff = not_xor.count('1')
        if diff < best_diff:
            character = BITMAPS[bitmap]
            best_diff = diff
            inverted = True

    if best_diff > 10:
        inverted = False
        character = u' \u2591\u2592\u2593\u2588'[
            min(4, len(fg_color) * 5 / 32)]

    if inverted:
        tmp = avg_bg_rgb
        avg_bg_rgb = avg_fg_rgb
        avg_fg_rgb = tmp

    return make_char(character, avg_fg_rgb, avg_bg_rgb)


def frame_to_ansi(frame):
    """Convert an image into 4x8 chunks and return ansi."""
    w, h = frame.size

    lines = (
        ''.join(
            (handle_pixel(frame, x, y) for x in range(0, w, 4))
        ) for y in range(0, h, 8)
    )
    ansi = ''.join(
        ('\x1b[0m', '\n'.join(lines))
    )

    return ansi


class RestoredTerminal(object):
    """Context manager to ensure we unbork the terminal."""

    def __enter__(self):
        pass

    def __exit__(self, exc_type, exc_val, exc_tb):
        print('\x1b[34h\x1b[?25h\x1b[0m\x1b[0m')


def is_url(img):
    """True if image is a url."""
    return img.startswith('http://') or img.startswith('https://')


def find_term_size():
    """Detect the size of the terminal we are running in.

    :return (int, int): columns, lines
    """
    col = 80
    lines = 24
    if get_terminal_size is not None:
        col, lines = get_terminal_size()
    else:
        try:
            col, lines = [
                int(i) for i in
                subprocess.check_output(["stty", "size"]).split()
            ]
        except Exception:
            pass
    return col, lines


def calculate_borders(bounding_width, bounding_height, original_width, original_height):
    """Calculate new dimensions that preserve the original aspect ratio and fit
    within the bounds given.

    :return (int, int): width, height
    """
    original_ratio = Fraction(original_width, original_height)
    bounding_ratio = Fraction(bounding_width, bounding_height)

    if original_ratio > bounding_ratio:
        new_height = Fraction(bounding_width, original_ratio)
        new_width = new_height * original_ratio
    else:
        new_width = bounding_height * original_ratio
        new_height = Fraction(original_height, original_width) * new_width

    new_width = min(int(round(new_width)), bounding_width)
    new_height = min(int(round(new_height)), bounding_height)

    return new_width, new_height


def main():
    col, lines = find_term_size()
    ap = argparse.ArgumentParser(
        epilog='Redirect this script\'s output to produce a bash script that '
        'plays the gif - suitable for sourcing from your .bashrc'
    )
    ap.add_argument(
        '-w', '--width', type=int, help='max width of file to show',
        default=col
    )
    ap.add_argument(
        '-h', '--height', type=int, help='max height of file to show',
        default=lines
    )
    ap.add_argument(
        '-f', '--forever', action='store_true', help='Loop forever'
    )
    ap.add_argument(
        '-d', '--delay', type=float, default=0.1,
        help='The delay between frames of a gif'
    )
    ap.add_argument(
        '-s', '--seperator', type=str,
        help='Print the seperator between frames of a gif (this can be useful '
             'if piping output into another file or program)'
    )
    ap.add_argument(
        'img', type=str, help='File or url to show'
    )
    args = ap.parse_args()

    if is_url(args.img):
        with requests.get(args.img, stream=True) as r:
            r.raise_for_status()
            img = Image.open(r.raw)
    else:
        with open(args.img) as f:
            img = Image.open(f)

    # img.load()

    new_size = calculate_borders(args.w, args.h, *img.size)
    total_frames = len([frame for frame in ImageSequence.Iterator(img)])
    frames = []
    for offset, frame in enumerate(ImageSequence.Iterator(img)):
        print(
            '\rLoading frames: {:.2f}% ({} of {})'
            ''.format(make_percent(offset, total_frames), offset, total_frames),
            file=sys.stderr, end=''
        )
        new_frame = Image.new('RGBA', frame.size)
        new_frame.paste(img, (0, 0), frame.convert('RGBA'))
        new_frame = new_frame.resize(new_size)
        frames.append(frame_to_ansi(new_frame))
    print('', file=sys.stderr)  # Clear the progress meter from stderr

    if os.isatty(sys.stdout.fileno()):
        if args.forever:
            frames = itertools.cycle(frames)
        try:
            with RestoredTerminal():
                for frame in frames:
                    print(
                        '\r\x1b[{h}A{frame}{sep}'
                        ''.format(
                            h=new_size[1], frame=frame, sep=args.seperator
                        ),
                        end=''
                    )
                    time.sleep(args.delay)
        except KeyboardInterrupt:
            sys.exit(128)
    else:
        # If we're not writing to a terminal, we're generating a bash script
        print('#!/usr/bin/env bash')
        for offset, frame in enumerate(frames):
            print(
                'cat <<FILE{offset}\n'
                '\r\x1b[{h}A{frame}{sep}\n'
                'FILE{offset}\n'
                'sleep {delay}\n'
                ''.format(
                    h=new_size[1], frame=frame, sep=args.seperator,
                    offset=offset, delay=args.delay
                ),
                end=''
            )
        print('printf \x1b[H\x1b[J')


if __name__ == '__main__':
    main()
