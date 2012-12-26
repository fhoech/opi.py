opi.py - OPI server in Python

Requirements
============

Python 2.5, 2.6 or 2.7
PIL 1.1.7 or later
Python for Windows extensions
wxPython

Usage
=====

python -u opi.py <options>

Call without options to get help.

Limitations
===========

Supports JPEG, PNG, PSD and TIFF images with 8 bits per pixel in CMYK (not
PSD), grayscale or RGB color mode (TIFF images with alpha channels, images
with 16 bits per pixel, or PSD images with layers or in CMYK are not [yet]
supported because of Python Imaging Library limitations).
EPS support.
Color management support with support for embedded profiles for JPEG, PNG and
TIFF image files.
When searching for image files, "special" characters look all the same to the
OPI parser - e.g. "Some special characters âáà.tif" and "Some special
characters ôóò.tif" are seen as the same. Check the logfile if you run into
problems.
Grayscale coloring has some issues - to circumvent, print as "DeviceN" in
QuarkXPress and place hires data in InDesign CS. Also, do not "colorize"
images with "white" in InDesign CS 2 and higher - use 0% black.
Tested with PostScript output from InDesign CS, CS 2, CS 3, QuarkXPress 6.5,
QuarkXPress 7 (Mac & Windows versions).
