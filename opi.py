#!/usr/bin/env python
# -*- coding: utf-8 -*-

# opi.py - Python OPI server

# Copyright (c) Florian Höch <fh(at)hoech.net>
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License as
# published by the Free Software Foundation; either version 3 of
# the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.



# Standard library imports
from codecs import BOM_UTF8
from decimal import Decimal
from difflib import get_close_matches
from hashlib import md5
from os import fdopen, listdir, mkdir, path, stat
from tempfile import gettempdir
from thread import start_new_thread
from time import gmtime, strftime, time
import binascii
import imghdr
import math
import os
import re
import struct
import sys
import traceback
if sys.platform == 'win32':
	import msvcrt
else:
	import tty
import zlib

# 3rd party imports
from PIL import (Image, ImageChops, ImageCms, ImageDraw, ImageFont, ImageOps,
				 JpegImagePlugin, PngImagePlugin, PsdImagePlugin, 
				 TiffImagePlugin)
if sys.platform == 'win32':
	import win32api
import wx

# Custom modules
from lib.ICCProfile import ICCProfile
from lib.LogWindow import LogWindow



class OPIparser:

	def __init__(self):	
		self.supportedtypes = ["epsf", "jpeg", "png", "psd", "tiff"]
		if "-epsf" in sys.argv[1:] or "-eps" in sys.argv[1:]:
			self.supportedtypes.remove("epsf")
		if "-jpeg" in sys.argv[1:] or "-jpg" in sys.argv[1:]:
			self.supportedtypes.remove("jpeg")
		if "-png" in sys.argv[1:]:
			self.supportedtypes.remove("png")
		if "-psd" in sys.argv[1:]:
			self.supportedtypes.remove("psd")
		if "-tiff" in sys.argv[1:] or "-tif" in sys.argv[1:]:
			self.supportedtypes.remove("tiff")
		self.wxApp = wx.PySimpleApp()
		self.build = strftime("%Y-%m-%d %H:%I:%S",
							  gmtime(os.stat(sys.argv[0]).st_mtime))
		self.console = None
		self.verbose = False
		self.abortonerror = True
		self.abortonfilenotfound = True
		self.convertcmykimages = False
		self.detectcmykgrayimages = True
		# Strip CMY if not converting
		self.cmykgrayimages_stripcmy = False
		self.convertgrayimages = False
		self.ICCProfiles = {}
		for key in ("proof", "proof_gray", "proof_RGB_gray", "out", "out_gray",
					"out_RGB_gray", "working_CMYK", "working_gray",
					"working_RGB"):
			self.ICCProfiles[key] = ICCProfile()
		self.sameprofiles_sets = []
		self.proofintent = "p"
		self.intent = "p"
		self.hirespath = ""
		self.lorespath = ""
		self.log = ""
		self.mode = "b"
		self.newline = "\n"
		self.usecache = True
		self.cachemegs = 256
		self.usediskcache = False
		self.version = [1.3, 2.0]
		self.imagecropthreshold = 1.1
		
		self.ColorImageDownsampleFilter = Image.ANTIALIAS
		self.GrayImageDownsampleFilter = Image.ANTIALIAS
		self.MonoImageDownsampleFilter = Image.ANTIALIAS
					
		self.DownsampleMonoImages = True
		self.MonoImageMinResolution = 800.0
		self.MonoImageResolution = 1200.0
		self.MonoImageUseEmbeddedResolution = True
		self.MonoImageDownsampleThreshold = 2.0
		self.DownsampleGrayImages = True
		self.GrayImageMinResolution = 200.0
		self.GrayImageResolution = 300.0
		self.GrayImageUseEmbeddedResolution = True
		self.GrayImageDownsampleThreshold = 2.0
		self.DownsampleColorImages = True
		self.ColorImageMinResolution = 200.0
		self.ColorImageResolution = 300.0
		self.ColorImageUseEmbeddedResolution = True
		self.ColorImageDownsampleThreshold = 2.0
		self.SmallHalftoneImageSize = 160 # pt
		self.SmallHalftoneImageResolutionFactor = 1.0
		self.TinyHalftoneImageSize = 80 # pt
		self.TinyHalftoneImageResolutionFactor = 1.0
		
		self._ImageCms_flags = []
		self._imagecache = {}
		self._cachebytes = 0
		self._max_occurrences = []
		self._transforms = {}
		
		# Example cmyk color definition with "Composite CMYK" / "Composite
		# Unchanged" (QuarkXPress 6.5 / 7):
		# 0 0 0 0 C
		# C M Y K
		
		self._qxpcolor_cmyk = re.compile("^((?:(?:\d+(?:\.\d+)?|\.\d+)\s+){4})C$")
		
		# Example spot color definition with "Composite CMYK" / "Composite
		# Unchanged" (QuarkXPress 6.5 / 7):
		# 0 0 0 0 (Spot Color Name)1 setcustc
		# C M Y K
		
		self._qxpcolor_cmykspot = re.compile("^((?:(?:\d+(?:\.\d+)?|\.\d+)\s+){4})\((.*)\)1 setcustc$")
		
		# Example rgb color definition with "Composite RGB" / "Composite
		# Unchanged" (QuarkXPress 6.5 / 7):
		# 0 0 0 R
		# R G B
		
		self._qxpcolor_rgb = re.compile("^((?:(?:\d+(?:\.\d+)?|\.\d+)\s+){3})R$")
		# Example lab spot color definition with "Composite Unchanged"
		# (QuarkXPress 6.5 / 7):
		# 1 [.5 .25 .5 ](Spot Color Name) genspotlab
		# GlobalTint [L a b]
		
		self._qxpcolor_labspot = re.compile("^((?:\d+(?:\.\d+)?|\.\d+)\s+)\[((?:(?:\d+(?:\.\d+)?|\.\d+)\s+){3})\]\(.+?\) genspotlab$")
		
		# Example spot color definition with "Composite RGB" / "Composite
		# Unchanged" (QuarkXPress 6.5 / 7):
		# 0 0 0 (Spot Color Name)1 setcustcrgb
		# R G B
		
		self._qxpcolor_rgbspot = re.compile("^((?:(?:\d+(?:\.\d+)?|\.\d+)\s+){3})\((.*)\)1 setcustcrgb$")
		
		# example spot color definition with DeviceN (QuarkXPress 6.5) /
		# "Composite CMYK and Spot" (QuarkXPress 7):
		# 1 1 [[0 0 1 0 ]][(Spot Color Name)]gendn
		# GlobalTint ColorTint [[C M Y K]]
		
		# example CMYK color definition with DeviceN (QuarkXPress 6.5) /
		# "Composite CMYK and Spot" (QuarkXPress 7):
		# 1 0 0 0 0 [[1 0 0 0 ][0 1 0 0 ][0 0 1 0 ][0 0 0 1 ]][(Cyan)(Magenta)(Yellow)(Black)]gendn
		# GlobalTint Color1Tint Color2Tint Color3Tint Color4Tint [[C1 M1 Y1 K1][C2 M2 Y2 K2][C3 M3 Y3 K3][C4 M4 Y4 K4]]
		
		self._qxpcolor_devicen = re.compile("^((?:(?:\d+(?:\.\d+)?|\.\d+)\s+){2,})\[((?:\[(?:(?:(?:\d+(?:\.\d+)?|\.\d+)\s+){4})\])+)\]\[((?:\(.+?\))+)\]gendn$")
		
		self._macshortpath = re.compile("\#[0-9a-fA-F]+(\..*)?$")
		self._qxpmarkbegin = None
		self._invalidchars = re.compile("[^\x20\x21\x23-\x29\x2b-\x3e\x40-\x7b\x7d\x7e]")
		# allow: \x2f = forward slash, \x3a = colon, \x3c = lesser-than sign
		# \x3e = greater-than sign, \x5c = backward slash
		# disallow: \x22 = quotation mark, \x2a = asterisk,
		# \x3f = question mark, \x7c = pipe
		self._invalidfnamechars = re.compile("[^\x20\x21\x23-\x29\x2b-\x2e\x30-\x39\x3b\x3d\x40-\x5b\\x5d-\x7b\x7d\x7e]")
		self._pschartags = re.compile("<[0-9a-fA-F]+>")
		self._psescapecodes = re.compile("\\\\\d+")
		self._spotcolors = {}
		self._creator = ""
		self._aborted = False
		self._terminated = False
		self._timestamp = time()
		self._stdin = None
		self._stdout = None
		self.errorcount = 0
		self.msgwindow = None
		self.frame = None

	def _reset(self):
		self._imgpath_md5 = None
		self._imagecached = None
		self._sizemod = None
		self._colormod = None
		self._iscmykgrayimage = None
		self._bgcolor = None
		self._errorstr = ""
		self._imageextension = ""
		self._imageformat = "[unknown]"
		self._cachelines = []
		self._BeginOPI = None
		self._version = []
		self._Distilled = None
		self._ImageFileName = ""
		self._ImageID = ""
		self._MainImage = ""
		self._ObjectComments = None
		self._BoundingBox = []
		self._ImageDimensions = []
		self._ImageCropRect = []
		self._ImageCropFixed = []
		
		self._RealCropRect = []
		self._RealDimensions = []
		self._RealRes = []
		self._DownsampleDimensions = []
		self._DownsampleFactor = [1.0, 1.0]
		self._DownsampleRes = []
		
		self._ImagePosition = []
		self._ImageResolution = []
		self._ImageColorType = None
		self._ImageColor = None
		self._ImageTint = None
		self._ImageOverprint = None
		self._ImageInks = None
		self._ImageType = []
		self._ImageGrayMap = []
		self._ImageGrayMap_ = None
		self._ImageTransparency = None
		self._TIFFASCIITags = {}
		self._TIFFASCIITag = None
		self._gfxstate = []
		self._original_gfxstate = []
		self._BeginIncludedImage = None
		self._IncludedImageDimensions = []
		self._IncludedImageQuality = 1.0
		self._object = None
		self._OPIobjectcount = 0
		self._BeginDocument = None

	def msg(self, txt, timestamp = True):
		if timestamp:
			s = time() - self._timestamp
			h = int(math.floor(s / 60 / 60))
			m = int(math.floor(s / 60))
			m -= h * 60
			s = int(round(s - (h * 60 * 60) - (m * 60)))
			if s >= 60:
				s -= 60
				m += 1
			if m >= 60:
				m -= 60
				h += 1
			txt = (str(h).zfill(2) + ":" + str(m).zfill(2) + ":" +
				   str(s).zfill(2) + " " + txt)
		self.console.write(txt)
		if self._fo != self._stdout:
			print txt.encode("utf-8", "backslashreplace")
		if self.log:
			self._log.write(txt.encode("utf-8", "backslashreplace") +
							self.newline)
			
	def escapefilename(self, filename = None):
		if not filename:
			filename = self._ImageFileName
		matches = self._invalidchars.findall(filename)
		for m in matches:
			filename = filename.replace(m,
										"<" +
										binascii.hexlify(m.encode('utf-8')) +
										">")
		return "(" + filename.replace("\\",
									  "\\\\").replace("(",
													  "\\(").replace(")",
																	 "\\)") + ")"

	def info(self):
		##self.msg("_cachelines: " + str(self._cachelines))  # DEBUG
		self.msg("_BeginOPI: " + str(self._BeginOPI))
		self.msg("_version: " + str(self._version))
		self.msg("_Distilled: " + str(self._Distilled))
		self.msg("_ImageFileName: " + self._ImageFileName)
		self.msg("_imgASCIIpath: " + self._imgASCIIpath)
		self.msg("_ObjectComments: " + str(self._ObjectComments))
		self.msg("_ImageDimensions: " + str(self._ImageDimensions))
		self.msg("_ImageCropRect: " + str(self._ImageCropRect))
		self.msg("_ImageCropFixed: " + str(self._ImageCropFixed))
		
		self.msg("_RealCropRect: " + str(self._RealCropRect))
		self.msg("_RealDimensions: " + str(self._RealDimensions))
		self.msg("_RealRes: " + str(self._RealRes))
		self.msg("_DownsampleDimensions: " + str(self._DownsampleDimensions))
		self.msg("_DownsampleFactor: " + str(self._DownsampleFactor))
		
		self.msg("_ImagePosition: " + str(self._ImagePosition))
		self.msg("_ImageResolution: " + str(self._ImageResolution))
		##self.msg("_bgcolor: " + str(self._bgcolor))  # Currently not used
		self.msg("_ImageColorType: " + str(self._ImageColorType))
		self.msg("_ImageColor: " + str(self._ImageColor))
		self.msg("_ImageTint: " + str(self._ImageTint))
		self.msg("_ImageOverprint: " + str(self._ImageOverprint))
		self.msg("_ImageInks: " + str(self._ImageInks))
		self.msg("_ImageType: " + str(self._ImageType))
		self.msg("_ImageGrayMap: " + str(self._ImageGrayMap))
		self.msg("_ImageTransparency: " + str(self._ImageTransparency))
		self.msg("_TIFFASCIITags: " + str(self._TIFFASCIITags))
		self.msg("_gfxstate: " + str(self._gfxstate))
		self.msg("_BeginIncludedImage: " + str(self._BeginIncludedImage))
		self.msg("_IncludedImageDimensions: " + str(self._IncludedImageDimensions))
		self.msg("_imagecache: " + str(self._imagecache))
		self.msg("_cachemegs: " + str(Decimal(str(round((self._cachebytes /
														 1024.0 / 1024.0) *
														100) / 100.0))))
		self.msg("_max_occurrences " + str(self._max_occurrences))
		
	def _raw_write(self, data):
		if not self._aborted:
			self._fo.write(data)
	
	def parse(self, fi, fo):
		
		if fi == "stdin":
			if sys.platform == 'win32':
				msvcrt.setmode(sys.stdin.fileno(), os.O_BINARY)
				self._stdin = self._fi = sys.stdin
			else:
				tty.setraw(sys.stdin.fileno())
				self._stdin = self._fi = fdopen(0, "rb")
		else:
			self._fi = open(fi, "rb")
		
		if fo == "stdout":
			if sys.platform == 'win32':
				msvcrt.setmode(sys.stdout.fileno(), os.O_BINARY)
				self._stdout = self._fo = sys.stdout
			else:
				tty.setraw(sys.stdout.fileno())
				self._stdout = self._fo = fdopen(1, "wb")
		else:
			self._fo = open(fo, "wb")
		
		self.console = LogWindow("pyOPI build " + str(self.build), (600, 600), "")
		start_new_thread(self.main, ())
		self.console.Show()
		self.wxApp.MainLoop()
		
	def main(self):
		try:
			if self.log:
				self._log = open(self.log, "wb")
				self._log.write(BOM_UTF8)
			self.msg("pyOPI build " + str(self.build), False)
			self.msg("Commandline options:", False)
			self.msg(self.newline.join(sys.argv[1:]) + self.newline, False)
			self.msg("Same profile sets:" + self.newline +
					 str(self.sameprofiles_sets) + self.newline, False)
			self._hirespath = path.split(self.hirespath)[1:]
			self._lorespath = path.split(self.lorespath)[1:]
		
			for key in self.ICCProfiles:
				if self.ICCProfiles[key].fileName:
					self.ICCProfiles[key].__init__(self.ICCProfiles[key].fileName)
			
			self._reset()
			self._parsemode = None
			for line in self._fi:
				while line:
					if self._terminated: break
					if not self._object:
						if self._parsemode != "a":
							self._parsemode = "a"
							if self.verbose:
								self.msg("Parsemode: Analyze" + self.newline)
						if not self._BeginOPI:
							i = line.find("%ALD")
							if i < 0: i = line.find("%%BeginOPI")
						else:
							i = line.find("%")
						if i >= 0:
							if i > 0:
								if not self._BeginOPI:
									self._raw_write(line[0:i])
								elif not self._BeginIncludedImage:
									self._cache(line[0:i])
									gfxstate = line[0:i].rstrip().splitlines()
									self._gfxstate += gfxstate
									self._original_gfxstate += gfxstate
									if self.verbose:
										self.msg("Cached GFX state: " +
												 self.newline.join(line[0:i].rstrip().splitlines()))
								line = line[i:]
							
							i = None
							r = line.find("\r")
							rn = line.find("\r\n")
							if r >= 0 and rn >= 0:
								if r < rn: i = r
								else: i = rn + 1
							elif r >= 0: i = r
							elif rn >= 0: i = rn + 1
							
							if i >= 0:
								self._parse(line[0:i+1])
								line = line[i+1:]
								
							else:
								self._parse(line)
								break
						else:
							if not self._BeginOPI:
								self._raw_write(line)
							elif not self._BeginIncludedImage:
								self._cache(line)
								gfxstate = line.rstrip().splitlines()
								self._gfxstate += gfxstate
								self._original_gfxstate += gfxstate
								if self.verbose:
									self.msg("Cached GFX state: " +
											 self.newline.join(line.rstrip().splitlines()))
							break
					else:
						if self._parsemode != "p":
							self._parsemode = "p"
							if self.verbose:
								if not self._BeginIncludedImage:
									self.msg("Parsemode: Pass-through")
								else:
									self.msg("Parsemode: Discard")
						i = line.find("%%End")
						if i < 0: i = line.find("%End")
						if i >= 0:
							i = line.find('%%End' + self._object)
							if i < 0:
								i = line.find('%End' + self._object.lower())
						if i >= 0:
							if self.verbose:
								self.msg('%%End' + self._object)
								self.msg("", False)
							self._object = None
							self._BeginDocument = None
							if not self._BeginIncludedImage:
								self._raw_write(line[0:i])
							line = line[i:]
						else:
							if not self._BeginIncludedImage:
								self._raw_write(line)
							break
				if self._terminated: break
			self._fi.close()
			if self._fo != self._stdout:
				self._fo.close()
			if self._aborted:
				if self._fo != self._stdout:
					self.msg(str(self.errorcount) +
							" ERROR(s) occured - empty PostScript output file "
							"generated.")
					# Make the output file 0 bytes
					self._fo = open(fo, "w")
					self._fo.close()
				else:
					self.msg(str(self.errorcount) +
							 " ERROR(s) occured - PostScript output will be "
							 "truncated because processing has been aborted.")
			elif self.errorcount > 0:
				self.msg("Done. " + str(self.errorcount) + " ERROR(s) occured.")
			else:
				self.msg("Done.")
			if self.log:
				self._log.close()
			if self.errorcount == 0 and not self._aborted:
				self.wxApp.ExitMainLoop()
		except Exception, v:
			self.msg("ERROR - unhandled exception: " + traceback.format_exc())
	
	def _abort(self):
		self._reset()
		self._aborted = True
		self.msg("", False)
	
	def _terminate(self, event = None):
		self._abort()
		if not self._terminated:
			self._terminated = True
			self.msg("Terminating...")
			self.msg("", False)
	
	def _parse(self, line):
		_line = line.strip()
		keys = _line.split(None, 1)
		n = 0
		for v in keys:
			keys[n] = keys[n].strip()
			n = n + 1
		
		if keys[0] == '%%BeginOPI:':
			self._BeginDocument = None
			self._cache(line)
			if self.verbose: self.msg("Cached: " + _line)
			self._OPIobjectcount += 1
			if self.verbose: self.msg("_OPIobjectcount: " +
									  str(self._OPIobjectcount))
			if not self._ImageFileName:
				self._BeginOPI = True
			self._version.append(float(keys[1]))
			self._BeginIncludedImage = False
			if not self._BeginOPI:
				self._raw_write(line)
		elif keys[0] in ('%ALDImageFileName:', '%ALDImageID:',
						 '%%ImageFileName:', '%%MainImage:'):
			self._BeginDocument = None
			if not self._ImageFileName:
				self._cache(line)
				if self.verbose: self.msg("Cached: " + unicode(_line, "cp1252",
															   "replace"))
				
				if keys[0] in ('%ALDImageFileName:', '%ALDImageID:'):
					self._version.append(1.3)
				self._BeginOPI = True
				
				# Image file names can have trailing spaces...
				keys = line.split(None, 1)
				# Strip trailing carriage return / newline
				keys[1] = keys[1].replace("\r", "").replace("\n", "")
				keys[1] = unicode(self._invalidchars.sub("?", keys[1]))
				if keys[1][0] == "(":
					# Strip parentheses
					keys[1] = keys[1][1:-1]
					# Replace double backslashes with pipe
					keys[1] = keys[1].replace("\\\\", "|")
					# Replace postscript escape codes with ? character
					keys[1] = self._psescapecodes.sub("?", keys[1])
					# Strip escaping backslashes
					keys[1] = keys[1].replace("\\", "")
					# Replace pipes with single backslashes
					keys[1] = keys[1].replace("|", "\\")
					# Replace postscript character tags with ? character
				keys[1] = self._pschartags.sub("?", keys[1])
				self._ImageFileName = keys[1]
				
				mac = 0
				posix = 0
				win = 0
				if self._ImageFileName.find("\\") > -1:
					# Windows
					win = 1
					imagepath = self._ImageFileName.split("\\")
				elif self._ImageFileName.find(':') > -1:
					# Mac OS 9
					mac = 1
					imagepath = self._ImageFileName.split(":")
				else:
					# Posix
					posix = 1
					imagepath = self._ImageFileName.split("/")

				# Remove drive letter / network share name / volume name
				imagepath.pop(0) 
				
				n = 0
				for p in self._lorespath:
					if n < len(imagepath) and p == imagepath[n]:
						imagepath.pop(0)
						n = n + 1
					else:
						break
		
				if n == 0:
					for p in self._hirespath:
						if n < len(imagepath) and p == imagepath[n]:
							imagepath.pop(0)
							n = n + 1
						else:
							break
				
				self.msg("Searching for image file: " +
						 joinpaths([self.hirespath] + imagepath))
				
				if not path.exists(joinpaths([self.hirespath] + imagepath)):
					if self._invalidchars.search(self._ImageFileName) or mac:
						# Handle filenames with high-ascii (32<>126) postscript
						# character escape codes via closest match approach
						n = -1
						for p in imagepath:
							n = n + 1
							if not path.exists(joinpaths([self.hirespath] + imagepath[0:n+1])):
								if mac and self._macshortpath.search(p):
									self.msg("Trying to resolve Mac OS 9 compatible file/foldername: " + p)
									p, ext = path.splitext(p)
									p = p.split("#")
									id = p.pop()  # File inode number
									p = "#".join(p)
									if n == 0:
										_path = self.hirespath
									else:
										_path = joinpaths([self.hirespath] + imagepath[0:n])
										if not path.exists(_path) or path.isfile(_path):
											_path = joinpaths([self.hirespath] + imagepath[0:n-1])
									if path.exists(_path):
										_dir = listdir(_path)
										_entry = ""
										if sys.platform == "win32":
											self.msg("Cannot use inode number (Windows), trying to find closest match using filename...")
											matches = get_close_matches(p + ext, _dir, 3, .6)
											if not len(matches):
												matches = get_close_matches(p + ext, _dir, 1, .6)
											if len(matches):
												if len(matches) > 1:
													self.errorcount += 1
													self.msg("ERROR: more than one match found for  \"" + p + "\":" + self.newline + self.newline.join(matches))
													if self.abortonfilenotfound:
														self._abort()
														return
													break
												else:
													_entry = imagepath[n] = matches[0]
													self.msg(p + " >> " + _entry)
											else:
												matches = get_close_matches(p + "#" + id + ext, _dir, 3, .6)
												if not len(matches):
													matches = get_close_matches(p + "#" + id + ext, _dir, 1, .6)
												if len(matches):
													if len(matches) > 1:
														self.errorcount += 1
														self.msg("ERROR: more than one match found for  \"" + p + "#" + id + ext + "\":" + self.newline + self.newline.join(matches))
														if self.abortonfilenotfound:
															self._abort()
															return
														break
													else:
														_entry = imagepath[n] = matches[0]
														self.msg(p + " >> " + _entry)
												else:
													self.errorcount += 1
													self.msg("ERROR: could not resolve Mac OS 9 compatible file/foldername \"" + p + "#" + id + ext + "\".")
													if self.abortonfilenotfound:
														self._abort()
														return
													break
										else:
											# Posix
											inode = binascii.unhexlify(id)
											if len(inode) == 1:
												inode = ord(inode)
											elif len(inode) == 2:
												inode = struct.unpack(">H", inode)[0]
											elif len(inode) == 4:
												inode = struct.unpack(">I", inode)[0]
											else:
												self.errorcount += 1
												self.msg("ERROR - could not resolve Mac OS 9 compatible file/foldername \"" + p + "#" + id + ext + "\": Invalid inode number " + id + ".")
												if self.abortonfilenotfound:
													self._abort()
													return
												break
											for item in _dir:
												if os.stat(path.join(_path, item)).st_ino == inode:
													_entry = imagepath[n] = item
													self.msg(p + " >> " + _entry)
											if not _entry:
												self.errorcount += 1
												self.msg("ERROR - could not resolve Mac OS 9 compatible file/foldername \"" + p + "#" + id + ext + "\": Inode " + id + " not found.")
												if self.abortonfilenotfound:
													self._abort()
													return
												break
									else:
										self.errorcount += 1
										self.msg("ERROR: path  \"" + _path + "\" does not exist.")
										if self.abortonfilenotfound:
											self._abort()
											return
										break
								else:
									# Start high-ASCII replacement
									self.msg("Trying to resolve file/foldername: " + p)
									_path = joinpaths([self.hirespath] + imagepath[0:n])
									if path.exists(_path):
										_dir = listdir(_path)
										_entry = ""
										matches = get_close_matches(p, _dir, 1, .6)
										if len(matches):
											if len(matches) > 1:
												self.errorcount += 1
												self.msg("ERROR: more than one match found for  \"" + p + "\":" + self.newline + self.newline.join(matches))
												if self.abortonfilenotfound:
													self._abort()
													return
												break
											else:
												_entry = imagepath[n] = matches[0]
												self.msg(p + " >> " + _entry)
										else:
											self.errorcount += 1
											self.msg("ERROR: could not resolve file/foldername \"" + p + "\".")
											if self.abortonfilenotfound:
												self._abort()
												return
											break
									else:
										self.errorcount += 1
										self.msg("ERROR: path  \"" + _path + "\" does not exist.")
										if self.abortonfilenotfound:
											self._abort()
											return
										break
									# End high-ASCII replacement
						
				self._imgASCIIpath = self._ImageFileName = joinpaths([self.hirespath] + imagepath)
				
				if (path.exists(self._ImageFileName) and
					path.isfile(self._ImageFileName)):
					self.msg("Image file found: " + self._ImageFileName)
					
					if (self._invalidchars.search(self._ImageFileName) and
						sys.platform == 'win32'):
						try:
							# Avoid various unicode related peculiarities with
							# PIL and Popen
							self._imgASCIIpath = win32api.GetShortPathName(self._ImageFileName) 
						except Exception, v:
							self.errorcount += 1
							self.msg("ERROR - win32api.GetShortPathName: " +
									 traceback.format_exc())
							if self.abortonfilenotfound:
								self._abort()
								return
					
					try:
						# WORKAROUND: imghdr does not support unicode filenames
						# directly (Python 2.4)
						imgfile = open(self._imgASCIIpath, "rb") 
						self._imageformat = imghdr.what(imgfile)
						if self._imageformat == "jpeg":
							self._imageextension = ".jpg"
						elif self._imageformat == "tiff":
							self._imageextension = ".tif"
						elif self._imageformat:
							self._imageextension = "." + self._imageformat
						else:
							imgfile.seek(0)
							data = imgfile.read(12)
							if (data[0:4] == "\xC5\xD0\xD3\xC6" or
								data[0:2] == "%!"):
								# DOS EPS Binary File or ASCII EPS File
								self._imageformat = "epsf"
								self._imageextension = ".eps"
							else:
								self._imageformat = "[unknown]"
					except IOerror:
						self._imageformat = "[unknown - error while reading file]"
					self.msg("Image type: " + str(self._imageformat))
					if self._imageformat not in self.supportedtypes:
						if self.verbose:
							self.msg("_cachelines: " + str(self._cachelines))
						self.msg("WARNING: image type not supported - passing "
								 "through remaining postscript data stream.")
						self.msg("         Please note it might contain highres"
								 " data, but it might also be lowres or empty.")
						self.msg("", False)
						self._writeCache()
						self._reset()
			elif not self._BeginOPI:
				self._raw_write(line)
			else:
				self._cache(line)
				if self.verbose: self.msg("Cached: " + unicode(_line, "cp1252",
															   "replace"))

		elif self._BeginOPI:
			if self._BeginIncludedImage:
				if keys[0] == '%%IncludedImageDimensions:':
					self._BeginDocument = None
					self._IncludedImageDimensions = intlist(keys[1].split(None))
				elif keys[0] == '%%BeginObject:':
					self._BeginDocument = None
					self._OPIobjectcount += 1
					if self.verbose:
						self.msg("_OPIobjectcount: " + str(self._OPIobjectcount))
				elif keys[0] in ('%%EndObject', '%%EndOPI'):
					self._BeginDocument = None
					self._OPIobjectcount -= 1
					if self.verbose:
						self.msg(keys[0])
						self.msg("_OPIobjectcount: " + str(self._OPIobjectcount))
					if self._OPIobjectcount == 0:
						self._write()
						self.msg("", False)
				else: self._parseskip(keys)
			else:
				self._BeginDocument = None
				self._cache(line)
				if self.verbose: self.msg("Cached: " + _line)
				if keys[0] == '%%Distilled':
					self._Distilled = True;
				elif keys[0] == '%ALDObjectComments:':
					self._ObjectComments = keys[1].split(None)
				elif keys[0] in ('%ALDImageDimensions:', '%%ImageDimensions:'):
					self._ImageDimensions = floatlist(keys[1].split(None))
				elif keys[0] == '%ALDImageCropRect:':
					self._ImageCropRect = intlist(keys[1].split(None))
					if not len(self._ImageCropFixed):
						self._ImageCropFixed = floatlist(keys[1].split(None))
				elif keys[0] in ('%ALDImageCropFixed:', '%%ImageCropRect:'):
					self._ImageCropFixed = floatlist(keys[1].split(None))
					if not len(self._ImageCropRect):
						self._ImageCropRect = intlist(keys[1].split(None))
				elif keys[0] == '%ALDImagePosition:':
					self._ImagePosition = floatlist(keys[1].split(None))
				elif keys[0] == '%ALDImageResolution:':
					self._ImageResolution = floatlist(keys[1].split(None))
				elif keys[0] == '%ALDImageColorType:':
					if (keys[1].lower() == "process" and self._ImageColor and
						(len(self._ImageColor) < 4 or
						 self._ImageColor[4] not in
						 ("Cyan", "Magenta", "Yellow", "Black"))):
						n = 0
						color = None
						for i, ink in enumerate(self._ImageColor):
							if ink > 0:
								if ink == 1:
									if n < 1:
										if i == 0: color = "Cyan"
										elif i == 1: color = "Magenta"
										elif i == 2: color = "Yellow"
										else: color = "Black"
									else: break
								n += 1
						if color and n == 1:
							self._ImageColor[4] = color
					self._ImageColorType = keys[1]
				elif keys[0] == '%ALDImageColor:':
					keys[1] = keys[1].split(None, 4)
					self._ImageColor = floatlist(keys[1][0:4])
					if len(keys[1]) < 4:
						keys[1].append("")
					elif keys[1][4][0] == "(":
						keys[1][4] = keys[1][4][1:-1]
					self._ImageColor.append(keys[1][4])
				elif keys[0] == '%ALDImageTint:':
					self._ImageTint = float(keys[1])
				elif keys[0] in ('%ALDImageOverprint:', '%%ImageOverprint:'):
					if keys[1].lower() == "true":
						self._ImageOverprint = True
					else:
						self._ImageOverprint = False
				elif keys[0] == '%ALDImageType:':
					self._ImageType = floatlist(keys[1].split(None))
				elif keys[0] == '%ALDImageGrayMap:':
					self._ImageGrayMap = [intlist(keys[1].split(None))]
					self._ImageGrayMap_ = self._ImageGrayMap
					self._TIFFASCIITag = None
				elif keys[0] == '%ALDImageTransparency:':
					if keys[1].lower() == "true":
						self._ImageTransparency = True
					else:
						self._ImageTransparency = False
				elif keys[0][0:17] == '%ALDImageAsciiTag':
					if len(keys) == 1:
						keys.append("")
					tagnumber = keys[0][17:-1]
					self._TIFFASCIITags[tagnumber] = [keys[1]]
					self._TIFFASCIITag = self._TIFFASCIITags[tagnumber]
					self._ImageGrayMap_ = None
				elif keys[0] == '%%TIFFASCIITag:':
					if len(keys) == 1:
						keys.append("")
					keys[1] = keys[1].split(None, 1)
					if len(keys[1]) == 0:
						keys[1].append("")
					if len(keys[1]) == 1:
						keys[1].append("")
					self._TIFFASCIITags[keys[1][0]] = [keys[1][1][1:-1]]
					self._TIFFASCIITag = self._TIFFASCIITags[keys[1][0]]
					self._ImageGrayMap_ = None
				elif keys[0] == '%%+':
					if len(keys) == 1:
						keys.append("")
					if self._TIFFASCIITag:
						if 2.0 in self.version:
							self._TIFFASCIITag.append(keys[1][1:-1])
						else:
							self._TIFFASCIITag.append(keys[1])
					elif self._ImageGrayMap_:
						self._ImageGrayMap_.append(intlist(keys[1].split(None)))
				elif keys[0] == '%%ImageInks:':
					self._ImageInks = keys[1]
				elif keys[0] == '%%BeginObject:':
					self._OPIobjectcount += 1
					if self.verbose:
						self.msg("_OPIobjectcount: " + str(self._OPIobjectcount))
					if keys[1] == 'image':
						self._BeginIncludedImage = True
				elif keys[0] == '%%BeginIncludedImage':
					self._BeginIncludedImage = True
				else:
					self._gfxstate.append(line.rstrip())
					self._original_gfxstate.append(line.rstrip())
		else: # not self._BeginOPI
			if not self._object:
				if not self._parseskip(keys):
					# This whole segment is currently never used by the parser.
					# Keep it here for reference, and because it contains some
					# legacy code which might be of use.
					if keys[0] in ('%%EndOPI', '%%EndObject'):
						self._reset()
					elif keys[0] == "%%Creator:" and not self._creator:
						if self.verbose: self.msg(keys[0] + " " + keys[1])
						keys[1] = keys[1].split("(")
						keys[1][0] = keys[1][0].strip()
						# Possible values:
						# Adobe InDesign CS
						# Adobe InDesign CS2
						# Adobe InDesign CS3
						if keys[1][0][0:14] == "Adobe InDesign":
							keys[1][0] = keys[1][0].split()
							self._creator = "ID" + keys[1][0][2]
							if self.verbose: self.msg(self._creator)
					elif keys[0] == '%%DocumentProcSets:' and not self._creator:
						if self.verbose: self.msg(keys[0] + " " + keys[1])
						keys[1] = keys[1].split(".")
						# Possible values:
						# QuarkXPress_6
						# QuarkXPress_7
						if keys[1][0][0:11] == "QuarkXPress":
							keys[1][0] = keys[1][0].split("_")
							self._creator = "QXP" + keys[1][0][1]
							if self.verbose: self.msg(self._creator)
					elif self._creator and self._creator[0:3] == "QXP":
						if _line == "1 H":
							# No background color - QuarkXPress 6.5 / 7
							# (Composite CMYK / Composite RGB / Composite
							# Unchanged)
							self._bgcolor = None
						elif self._qxpcolor_cmyk.search(_line):
							# CMYK background color - QuarkXPress 6.5 / 7
							# (Composite CMYK / Composite Unchanged)
							color = floatlist(_line.split(None)[0:4])
							self._bgcolor = []
							inknames = ["Cyan", "Magenta", "Yellow", "Black"]
							for i, ink in enumerate(color):
								if (ink > 0):
									inks = [0.0, 0.0, 0.0, 0.0]
									inks[i] = 1.0
									self._bgcolor.append([ink, inks,
														  inknames[i]])
						elif self._qxpcolor_cmykspot.search(_line):
							# cmyk spot background color - QuarkXPress 6.5 / 7
							# (Composite CMYK / Composite Unchanged)
							color = strlist(self._qxpcolor_cmykspot.search(_line).groups())
							self._bgcolor = [[1.0,
											  floatlist(color[0].split(None)[0:4]),
											  color[1]]]
						elif self._qxpcolor_labspot.search(_line):
							self._bgcolor = None # TO-DO
						elif self._qxpcolor_rgb.search(_line):
							# rgb background color - QuarkXPress 6.5 / 7
							# (Composite RGB / Composite Unchanged)
							color = floatlist(_line.split(None)[0:3])
							self._bgcolor = []
							inknames = ["Red", "Green", "Blue"]
							for i, ink in enumerate(color):
								if (ink > 0):
									inks = [0, 0, 0]
									inks[i] = 1.0
									self._bgcolor.append([ink, inks,
														  inknames[i]])
						elif self._qxpcolor_rgbspot.search(_line):
							# RGB spot background color - QuarkXPress 6.5 / 7
							# (Composite RGB / Composite Unchanged)
							color = strlist(self._qxpcolor_rgbspot.search(_line).groups())
							self._bgcolor = [[1.0,
											  floatlist(color[0].split(None)[0:3]),
											  color[1]]]
						elif self._qxpcolor_devicen.search(_line):
							# Background color - QuarkXPress 6.5 (DeviceN) / 7
							# (Composite CMYK + Spot)
							color = strlist(self._qxpcolor_devicen.search(_line).groups())
							color[0] = floatlist(color[0].strip().split(None))
							color[1] = color[1][1:-1].strip().split("][")
							color[2] = color[2][1:-1].strip().split(")(")
							self._bgcolor = []
							for i in xrange(len(color[1])):
								color[1][i] = floatlist(color[1][i].strip().split(None))
								if (color[1][i] != [0.0, 0.0, 0.0, 0.0] and
									color[0][0] * color[0][i + 1] > 0):
									self._spotcolors[color[2][i]] = color[1][i]
									self._bgcolor.append([color[0][0] *
														  color[0][i + 1],
														  color[1][i],
														  color[2][i]])
			else:
				self._BeginDocument = None
			self._raw_write(line)
			
	def _parseskip(self, keys):
		_line = " ".join(keys)
		if (keys[0] in ('%%BeginBinary:', '%%BeginData:', '%%BeginDefaults',
						'%%BeginDocument:', '%%BeginFont:',
						'%%BeginIncludedImage', '%%BeginObject:',
						'%%BeginPageSetup', '%BeginPhotoshop:', '%%BeginProlog',
						'%%BeginResource:', '%%BeginSetup') or
			(keys[0][0:10] == "%!PS-Adobe" and self._BeginDocument and
			 len(keys) == 2)):
			if keys[0][0:10] == "%!PS-Adobe":
				if keys[1][0:4] == "EPSF":
					self._object = "Document"
					if self.verbose:
						self.msg(self._BeginDocument)
						self.msg(_line)
				self._BeginDocument = None
			elif keys[0] == '%%BeginDocument:':
				self._BeginDocument = _line
			else:
				if keys[0][-1] == ":": keys[0] = keys[0][0:-1]
				self._object = keys[0].replace("%", "")[5:]
				self._BeginDocument = None
				if self.verbose: self.msg(_line)
			return True
		else:
			self._BeginDocument = None
			return False

	def _cache(self, line):
		self._cachelines.append(line)

	def _writeCache(self):
		self._raw_write("".join(self._cachelines))
		self._cachelines = []

	def _failimage(self, errorstr):
		self.msg(errorstr)
		self.msg("Creating placeholder image...")
		image = Image.new("CMYK", (320, 240), (0, 255, 255, 0))
		draw = ImageDraw.Draw(image)
		draw.line((0, 0) + image.size, fill = (0, 0, 0, 255))
		draw.line((0, image.size[1], image.size[0], 0), fill = (0, 0, 0, 255))
		errorstr = errorstr.split(":", 1)
		errorstr[0] = errorstr[0] + ":"
		if len(errorstr) < 2:
			errorstr.append("<>")
		try:
			font = ImageFont.truetype('arial.ttf', 12)
		except IOError:
			font = ImageFont.load_default()
		x1 = image.size[0] - (image.size[0] / 2) - (font.getsize(errorstr[0])[0] / 2)
		y1 = image.size[1] - (image.size[1] / 2) - font.getsize(errorstr[0])[1]
		x2 = image.size[0] - (image.size[0] / 2) - (font.getsize(errorstr[1])[0] / 2)
		y2 = image.size[1] - (image.size[1] / 2)
		draw.rectangle([0, y1, image.size[0],
					   y2 + font.getsize(errorstr[1])[1]],
					   outline=(0, 255, 255, 0), fill=(0, 255, 255, 0))
		draw.text((x1, y1), errorstr[0], font = font, fill = (0, 0, 0, 0))
		draw.text((x2, y2), errorstr[1], font = font, fill = (0, 0, 0, 0))
		del draw
		self._DownsampleDimensions =  [image.size[0], image.size[1]]
		self._DownsampleFactor =  [1.0, 1.0]
		self._ImageCropFixed = [0, 0, image.size[0], image.size[1]]
		self._ImageCropRect = [0, 0, image.size[0], image.size[1]]
		self._IncludedImageDimensions =  [image.size[0], image.size[1]]
		self._RealCropRect = [0, 0, image.size[0], image.size[1]]
		return image

	def _gettmppath(self, cachedirname = None):
		# Build filename from hash of original filename
		fpath = path.dirname(self._imgASCIIpath)
		fname = path.basename(self._ImageFileName)
		if self._imagecached:
			cachedir = fpath
		else:
			if cachedirname:
				cachedir = path.join(fpath, cachedirname)
			else:
				cachedir = path.join(fpath, self._getICCconf())
		if (self.usediskcache and path.exists(fpath) and
			not path.exists(cachedir)):
			mkdir(cachedir)
		_tmppath = path.join(cachedir,  self._invalidfnamechars.sub("_", fname))
		return _tmppath
	
	def _detectcmykgrayimages(self):
		if (self._getimage().mode == "CMYK" and self.detectcmykgrayimages and
			(((self.convertcmykimages or self.convertgrayimages) and
			  self.ICCProfiles["out"].fileName) or
			 (self.convertgrayimages and
			  self.ICCProfiles["out_gray"].fileName) or
			 self.cmykgrayimages_stripcmy)):
			# Detecting CMYK gray images only makes sense if:
			#  - the image is CMYK (obviously)
			#  - convertcmykimages is True and outprofile is set
			#    (prevent K->CMYK transformation), OR convertgrayimages is True
			#    and out(gray)profile is set,
			#    OR cmykgrayimages_stripcmy is True (strip CMY to reduce overhead)
			# so, detect CMYK gray images if:
			#  - the above is True
			#  - detectcmykgrayimages is True
			
			# Test for "K only" CMYK image
			self.msg("Checking if CMYK image is really a grayscale image...")
			# First test 5 pixels, if they are all equal, test the whole image
			# 1   2
			#   3
			# 4   5
			w, h = self._getimage().size
			test1 = self._getimage().getpixel((w / 4, h / 4))
			if test1[0] == test1[1] == test1[2] == 0:
				test2 = self._getimage().getpixel(((w / 4) * 3, (h / 4)))
				if test2[0] == test2[1] == test2[2] == 0:
					test3 = self._getimage().getpixel((w / 2, h / 2))
					if test3[0] == test3[1] == test3[2] == 0:
						test4 = self._getimage().getpixel(((w / 4),
														   (h / 4) * 3))
						if test4[0] == test4[1] == test4[2] == 0:
							test5 = self._getimage().getpixel(((w / 4) * 3,
															   (h / 4) * 3))
							if test5[0] == test5[1] == test5[2] == 0:
								# Get channels of image
								channels = self._getimage().split()
								# Create white CMYK image in the same size as 
								# our real image
								img = Image.new("CMYK",
												(self._getimage().size[0],
												 self._getimage().size[1]),
												(0, 0, 0, 0))
								# Get first channel of created image
								zero = img.split()[0].tostring()
								# Compare channels to see if C, M, Y are empty
								if (zero == channels[0].tostring() ==
									channels[1].tostring() ==
									channels[2].tostring()):
									# Monochrome image
									self._iscmykgrayimage = True
									self.msg("CMYK image is really a grayscale "
											 "image (CMY channels are empty).")
									if ((not self.convertgrayimages or
										 not (self.ICCProfiles["out_gray"].fileName or
										 self.ICCProfiles["out"].fileName)) and
										self.cmykgrayimages_stripcmy):
										self.msg("Stripping CMY...")
										try:
											self._setimage(ImageChops.invert(Image.merge("L", [channels[3]])))
										except Exception, v:
											self.errorcount += 1
											self.msg("ERROR - fatal error while"
													 "processing image: " + traceback.format_exc())
											self.msg("Try re-saving the image"
													 "from your imaging "
													 "application.")
											self._abort()
										return ""

	def profiles_same(self, *profiles):
		sameprofiles = {}
		def add(key, *profiles):
			if not key in sameprofiles:
				sameprofiles[key] = []
			for profile in profiles:
				if not profile in sameprofiles[key]:
					sameprofiles[key].append(profile)
		for profile in profiles[1:]:
			if profiles[0].isSame(profile):
				self.msg("These profiles have identical IDs: %s (ID %s), %s (ID %s)" % 
						 (profiles[0].getDescription(), 
						  binascii.hexlify(profiles[0].ID), 
						  profile.getDescription(), 
						  binascii.hexlify(profile.ID)))
				add(profiles[0].ID, profiles[0], profile)
				continue
			for index, desc_or_md5_set in enumerate(self.sameprofiles_sets):
				if (profiles[0].getDescription() in desc_or_md5_set and 
					profile.getDescription() in desc_or_md5_set) or \
				   (profiles[0].ID in desc_or_md5_set and 
					profile.ID in desc_or_md5_set):
					self.msg("These profiles are the same: %s (ID %s), %s (ID %s)" % 
							 (profiles[0].getDescription(), 
							  binascii.hexlify(profiles[0].ID), 
							  profile.getDescription(), 
							  binascii.hexlify(profile.ID)))
					add(index, profiles[0], profile)
		return sameprofiles
	
	def _ICCtransform(self):
		srcprofile = None
		proofintent = 0
		proofprofile = None
		intent = 0
		profile = None
		if ((self.ICCProfiles["out"].fileName and
			 (self._getimage().mode == "RGB" or
			  (self._getimage().mode == "CMYK" and self.convertcmykimages and
			   not (self._iscmykgrayimage and
					self.ICCProfiles["out_gray"].fileName)))) or
			((self.ICCProfiles["out_gray"].fileName or
			  self.convertgrayimages) and 
			 (self._getimage().mode == "L" or self._iscmykgrayimage)) or
			(self.ICCProfiles["out_RGB_gray"].fileName and
			 self._getimage().mode == "RGB")):
			self.msg("Getting source profile...")
			if (self._getimage().info.has_key("icc_profile") and
				len(self._getimage().info["icc_profile"]) > 0):
				srcprofile = ICCProfile(self._getimage().info["icc_profile"])
				srcprofile.calculateID()
				srcprofile.fileName = path.join(gettempdir(),
												binascii.hexlify(srcprofile.ID)
												+ '.icc')
			else:
				self.msg("...none found, falling back to working spaces (if "
						 "defined)")
				if self._getimage().mode == "CMYK":
					srcprofile = self.ICCProfiles["working_CMYK"]
				elif self._getimage().mode == "L":
					srcprofile = self.ICCProfiles["working_gray"]
				elif self._getimage().mode == "RGB":
					srcprofile = self.ICCProfiles["working_RGB"]

			if not srcprofile.data:
				self.msg("...no source profile, skipping color conversion")
			else:
				self.msg("Source profile: " + srcprofile.getDescription())
				self.msg("Determining destination profile...")
				# Determine which profiles to use
				if (self._getimage().mode == "RGB" or
					(self._getimage().mode == "CMYK" and
					 self.convertcmykimages and
					 not (self._iscmykgrayimage and
						  self.ICCProfiles["out_gray"].fileName))):
					if (self._getimage().mode == "RGB" and
						(self.ICCProfiles["proof_RGB_gray"].fileName or
						 self.ICCProfiles["out_RGB_gray"].fileName)):
						self.msg("Checking if image is R=G=B...")
						# Allow converting of "R=G=B" images to grayscale or
						# special "monochrome" profile (which could be grayscale
						# or max GCR CMYK for example)
						# First we test 5 pixels, if they are all equal, we test
						# the whole image
						# 1   2
						#   3
						# 4   5
						w, h = self._getimage().size
						test1 = self._getimage().getpixel((w / 4, h / 4))
						if test1[0] == test1[1] == test1[2]:
							test2 = self._getimage().getpixel(((w / 4) * 3,
															   (h / 4)))
							if test2[0] == test2[1] == test2[2]:
								test3 = self._getimage().getpixel((w / 2,
																   h / 2))
								if test3[0] == test3[1] == test3[2]:
									test4 = self._getimage().getpixel(((w / 4),
																	   (h / 4) * 3))
									if test4[0] == test4[1] == test4[2]:
										test5 = self._getimage().getpixel(((w / 4) * 3,
																		   (h / 4) * 3))
										if test5[0] == test5[1] == test5[2]:
											red, green, blue = [channel.tostring()
																for channel in
																self._getimage().split()]
											if red == green == blue:
												# it's a monochrome image
												self.msg("RGB image is an "
														 "'R=G=B' image "
														 "(identical channels)")
												if self.ICCProfiles["proof_RGB_gray"].fileName:
													self.msg("...using 'RGB gray' proofing profile")
													proofprofile = self.ICCProfiles["proof_RGB_gray"]
												if self.ICCProfiles["out_RGB_gray"].fileName:
													self.msg("...using 'RGB gray' destination profile")
													profile = self.ICCProfiles["out_RGB_gray"]
												if profile.colorSpace == "GRAY":
													self._ImageColorType = "Process"
													self._ImageColor = [0, 0, 0, 1, "Black"]
													self._ImageTint = 1.0
													self._ImageInks = "monochrome 1 (Black) 1.0"
				else:
					if self.ICCProfiles["proof_gray"].fileName:
						self.msg("...using gray proofing profile")
						proofprofile = self.ICCProfiles["proof_gray"]
					if self.ICCProfiles["out_gray"].fileName:
						self.msg("...using gray destination profile")
						profile = self.ICCProfiles["out_gray"]
				if not proofprofile:
					proofprofile = self.ICCProfiles["proof"]
				if not profile:
					profile = self.ICCProfiles["out"]
				
				if not profile.data:
					self.msg("...no destination profile set, skipping color "
							 "conversion")
				else:
					self.msg("Destination profile: " + profile.getDescription())
					if proofprofile.data:
						self.msg("Proofing profile: " + proofprofile.getDescription())
						if self.profiles_same(srcprofile, proofprofile):
							if self.profiles_same(profile, proofprofile):
								self.msg("Source profile is the same as "
										 "proofing and destination profile, "
										 "skipping color conversion")
							else:
								self.msg("Source profile is the same as "
										 "proofing profile, skipping proofing "
										 "color tranform")
						elif self.profiles_same(profile, proofprofile):
							self.msg("Proofing profile is the same as "
									 "destination profile, skipping proofing "
									 "color tranform")
					elif self.profiles_same(srcprofile, profile):
						self.msg("Source profile is the same as destination "
								 "profile, skipping color conversion")
				
				if (profile.data and
					(not self.profiles_same(srcprofile, profile) or
					 (proofprofile.data and 
					  not self.profiles_same(srcprofile, proofprofile)))):
					
					flags = self._ImageCms_flags
					
					# Output transform
					if self.intent[0] == "a":
						intent = 3
					if self.intent[0] == "b":
						intent = 1
						flags.append(ImageCms.FLAGS["BLACKPOINTCOMPENSATION"])
					elif self.intent[0] == "r":
						intent = 1
					elif self.intent[0] == "s":
						intent = 2
					else:
						intent = 0
					
					# Proofing transform
					if ((self.ICCProfiles["proof"].fileName and 
						 (self._getimage().mode == "RGB" or
						  (self._getimage().mode == "CMYK" and
						   self.convertcmykimages and
						   not self._iscmykgrayimage))) or
						(self.ICCProfiles["proof_gray"].fileName and
						 (self._getimage().mode == "L" or
						  self._iscmykgrayimage)) or 
						(self.ICCProfiles["proof_RGB_gray"].fileName and
						 self._getimage().mode == "RGB")):
						
						flags.append(ImageCms.FLAGS["SOFTPROOFING"])
						
						if self.proofintent[0] == "a":
							proofintent = 3
						if self.proofintent[0] == "b":
							proofintent = 1
							flags.append(ImageCms.FLAGS["BLACKPOINTCOMPENSATION"])
						elif self.proofintent[0] == "r":
							proofintent = 1
						elif self.proofintent[0] == "s":
							proofintent = 2
						else:
							proofintent = 0
					
					flag_bitmask = 0
					for flag_bit in flags:
						flag_bitmask |= flag_bit
					
					t_hash = md5(str(srcprofile.fileName) + chr(0) + str(intent)
								 + chr(0) + str(profile.fileName) + chr(0) +
								 str(proofintent) + chr(0) +
								 str(proofprofile.fileName)).hexdigest()
					if not self._transforms.has_key(t_hash):
						if not path.exists(srcprofile.fileName):
							f = open(srcprofile.fileName, "wb")
							f.write(srcprofile.data)
							f.close()
						if proofprofile.data:
							if self.profiles_same(profile, proofprofile):
								proofprofile = None
						if profile.colorSpace == "GRAY":
							dstmode = "L"
						elif profile.colorSpace in ("RGB", "CMYK"):
							dstmode = profile.colorSpace
						else:
							self.msg("Unsupported profile color space '%s' - "
									 "aborting..." % profile.colorSpace)
							self._abort()
							return
						srcprofile_obj = ImageCms.ImageCmsProfile(srcprofile.fileName)
						dstprofile_obj = ImageCms.ImageCmsProfile(profile.fileName)
						if proofprofile and proofprofile.data:
							proofprofile_obj = ImageCms.ImageCmsProfile(proofprofile.fileName)
							transform = ImageCms.ImageCmsTransform(srcprofile_obj,
																   dstprofile_obj,
																   self._getimage().mode,
																   dstmode,
																   intent,
																   proofprofile_obj,
																   proofintent,
																   flag_bitmask)
						else:
							transform = ImageCms.ImageCmsTransform(srcprofile_obj,
																   dstprofile_obj,
																   self._getimage().mode,
																   dstmode,
																   intent,
																   None,
																   0,
																   flag_bitmask)
						self._transforms[t_hash] = transform
					else:
						transform = self._transforms[t_hash]
					self.msg("Color converting image...")
					info = self._getimage().info.copy()
					self._setimage(transform.apply(self._getimage()))
					info["icc_profile"] = profile.data
					self._getimage().info = info
				
	
	def _getICCconf(self):
		conf = ""
		intents = {"a": "Absolute",
				   "b": "RelativeWithBPC",
				   "p": "Perceptual",
				   "r": "Relative",
				   "s": "Saturation"}
		if (self.ICCProfiles["proof"].fileName or
			self.ICCProfiles["proof_gray"].fileName or
			self.ICCProfiles["proof_RGB_gray"].fileName):
			conf += "ProofIntent_" + str(intents[self.proofintent])
			if (self.ICCProfiles["proof"].fileName):
				conf += "_ProofProfile_" + path.splitext(path.basename(self.ICCProfiles["proof"].fileName))[0]
			if (self.ICCProfiles["proof_gray"].fileName):
				conf += "_ProofGrayProfile_" + path.splitext(path.basename(self.ICCProfiles["proof_gray"].fileName))[0]
			if (self.ICCProfiles["proof_RGB_gray"].fileName):
				conf += "_ProofRGBGrayProfile_" + path.splitext(path.basename(self.ICCProfiles["proof_RGB_gray"].fileName))[0]
		if (self.ICCProfiles["out"].fileName or self.ICCProfiles["out_gray"].fileName or self.ICCProfiles["out_RGB_gray"].fileName):
			if conf:
				conf += "_"
			conf += "Intent=" + str(intents[self.intent])
			if (self.ICCProfiles["out"].fileName):
				conf += "_Profile=" + path.splitext(path.basename(self.ICCProfiles["out"].fileName))[0]
			if (self.ICCProfiles["out_gray"].fileName):
				conf += "_GrayProfile=" + path.splitext(path.basename(self.ICCProfiles["out_gray"].fileName))[0]
			if (self.ICCProfiles["out_RGB_gray"].fileName):
				conf += "_RGBGrayProfile=" + path.splitext(path.basename(self.ICCProfiles["out_RGB_gray"].fileName))[0]
			if (self.ColorImageResolution == self.GrayImageResolution and
				not self.ColorImageUseEmbeddedResolution and
				not self.GrayImageUseEmbeddedResolution):
				conf += "_" + str(int(round(self.ColorImageResolution))) + "dpi"
		return conf.replace(" ", "")
	
	def _getimageconf(self, sizemod, colormod, iccmod = True):
		# The "image configuration" is all the stuff that is not read from the image file itself
		conf = ""
		if iccmod:
			conf += ",proofintent:" + str(self.proofintent)
			conf += ",proofgrayprofile:" + str(self.ICCProfiles["proof_gray"].fileName)
			conf += ",proofRGBgrayprofile:" + str(self.ICCProfiles["proof_RGB_gray"].fileName)
			conf += ",proofprofile:" + str(self.ICCProfiles["proof"].fileName)
			conf += ",intent:" + str(self.intent)
			conf += ",outgrayprofile:" + str(self.ICCProfiles["out_gray"].fileName)
			conf += ",outRGBgrayprofile:" + str(self.ICCProfiles["out_RGB_gray"].fileName)
			conf += ",outprofile:" + str(self.ICCProfiles["out"].fileName)
			conf += ",convertcmykimages:" + str(self.convertcmykimages)
			conf += ",convertgrayimages:" + str(self.convertgrayimages)
			conf += ",detectcmykgrayimages:" + str(self.detectcmykgrayimages)
		conf += ",MonoImageMinResolution:" + str(self.MonoImageMinResolution)
		conf += ",MonoImageResolution:" + str(self.MonoImageResolution)
		conf += ",MonoImageDownsampleThreshold:" + str(self.MonoImageDownsampleThreshold)
		conf += ",GrayImageMinResolution:" + str(self.GrayImageMinResolution)
		conf += ",GrayImageResolution:" + str(self.GrayImageResolution)
		conf += ",GrayImageDownsampleThreshold:" + str(self.GrayImageDownsampleThreshold)
		conf += ",ColorImageMinResolution:" + str(self.ColorImageMinResolution)
		conf += ",ColorImageResolution:" + str(self.ColorImageResolution)
		conf += ",ColorImageDownsampleThreshold:" + str(self.ColorImageDownsampleThreshold)
		if sizemod:
			if self._ImageCropFixed:
				conf += ",ImageCropFixed:" + str(self._ImageCropFixed)
			if self._RealDimensions:
				conf += ",RealDimensions:" + str(self._RealDimensions)
		if colormod:
			if self._ImageColor:
				conf += ",ImageColor:" + str(self._ImageColor)
			if self._bgcolor:
				conf += ",bgcolor:" + str(self._bgcolor)
		if self.verbose: self.msg(conf)
		return conf
	
	def _SetDownsampleDimensions(self):
		if self._RealDimensions:
			if self._getimage().mode != "1":
				if (max(self._RealDimensions[0], self._RealDimensions[1]) <=
					self.TinyHalftoneImageSize):
					imagesizefactor = self.TinyHalftoneImageResolutionFactor
				elif (max(self._RealDimensions[0], self._RealDimensions[1]) <=
					  self.SmallHalftoneImageSize):
					imagesizefactor = self.SmallHalftoneImageResolutionFactor
				else:
					imagesizefactor = 1.0
			if self._getimage().mode == "1" and self.DownsampleMonoImages:
				if (self._getimage().info.has_key("dpi") and
					self.MonoImageUseEmbeddedResolution and
					min(self._getimage().info["dpi"][0],
						self._getimage().info["dpi"][1]) >
					self.MonoImageResolution):
					self._DownsampleRes = self._getimage().info["dpi"]
					if self.verbose:
						self.msg("_SetDownsampleDimensions: Using image dpi " +
								 str(self._DownsampleRes))
				else:
					self._DownsampleRes = (self.MonoImageResolution,
										   self.MonoImageResolution)
					if self.verbose:
						self.msg("_SetDownsampleDimensions: Using "
								 "MonoImageResolution " +
								 str(self._DownsampleRes))
				if (self._RealRes[0] >
					self._DownsampleRes[0] * self.MonoImageDownsampleThreshold):
					self._DownsampleDimensions[0] = (self._RealDimensions[0] / 72.0) * self._DownsampleRes[0]
				if (self._RealRes[1] >
					self._DownsampleRes[1] * self.MonoImageDownsampleThreshold):
					self._DownsampleDimensions[1] = (self._RealDimensions[1] / 72.0) * self._DownsampleRes[1]
			elif self._getimage().mode == "L" and self.DownsampleGrayImages:
				if (self._getimage().info.has_key("dpi") and
					self.GrayImageUseEmbeddedResolution and
					min(self._getimage().info["dpi"][0],
						self._getimage().info["dpi"][1]) >
					self.GrayImageResolution):
					self._DownsampleRes = self._getimage().info["dpi"]
					if self.verbose:
						self.msg("_SetDownsampleDimensions: Using image dpi " +
								 str(self._DownsampleRes))
				else:
					self._DownsampleRes = (self.GrayImageResolution,
										   self.GrayImageResolution)
					if self.verbose:
						self.msg("_SetDownsampleDimensions: Using "
								 "GrayImageResolution " +
								 str(self._DownsampleRes))
				if (self._RealRes[0] >
					self._DownsampleRes[0] * self.GrayImageDownsampleThreshold *
					imagesizefactor):
					self._DownsampleDimensions[0] = (self._RealDimensions[0] / 72.0) * self._DownsampleRes[0] * imagesizefactor
				if (self._RealRes[1] > self._DownsampleRes[1] *
					self.GrayImageDownsampleThreshold * imagesizefactor):
					self._DownsampleDimensions[1] = (self._RealDimensions[1] / 72.0) * self._DownsampleRes[1] * imagesizefactor
			elif (self._getimage().mode in ("RGB", "CMYK") and
				  self.DownsampleColorImages):
				if (self._getimage().info.has_key("dpi") and
					self.ColorImageUseEmbeddedResolution and
					min(self._getimage().info["dpi"][0],
						self._getimage().info["dpi"][1]) >
					self.ColorImageResolution):
					self._DownsampleRes = self._getimage().info["dpi"]
					if self.verbose:
						self.msg("_SetDownsampleDimensions: Using image dpi " +
								 str(self._DownsampleRes))
				else:
					self._DownsampleRes = (self.ColorImageResolution,
										   self.ColorImageResolution)
					if self.verbose:
						self.msg("_SetDownsampleDimensions: Using "
								 "ColorImageResolution " + 
								 str(self._DownsampleRes))
				if (self._RealRes[0] > self._DownsampleRes[0] *
					self.ColorImageDownsampleThreshold * imagesizefactor):
					self._DownsampleDimensions[0] = (self._RealDimensions[0] / 72.0) * self._DownsampleRes[0] * imagesizefactor
				if (self._RealRes[1] > self._DownsampleRes[1] *
					self.ColorImageDownsampleThreshold * imagesizefactor):
					self._DownsampleDimensions[1] = (self._RealDimensions[1] / 72.0) * self._DownsampleRes[1] * imagesizefactor
			if self._ImageCropFixed:
				croppedsize = [self._ImageCropFixed[2] - self._ImageCropFixed[0],
							   self._ImageCropFixed[3] - self._ImageCropFixed[1]]
			else:
				croppedsize = floatlist(self._getimage().size)
			self._DownsampleFactor = [self._DownsampleDimensions[0] / croppedsize[0],
									  self._DownsampleDimensions[1] / croppedsize[1]]
			if 2.0 in self._version:
				# Assume QuarkXPress
				self._DownsampleDimensions = [int(math.ceil(self._getimage().size[0] *
															self._DownsampleFactor[0])),
											  int(math.ceil(self._getimage().size[1] *
															self._DownsampleFactor[1]))]
			else:
				self._DownsampleDimensions = [int(round(self._getimage().size[0] *
														self._DownsampleFactor[0])),
											  int(round(self._getimage().size[1] *
														self._DownsampleFactor[1]))]
	
	def _CropAndDownsample(self):
		cropped = False
		imagecopy = False
		self._sizemod  = False
		endsize = [self._RealCropRect[2] - self._RealCropRect[0],
				   self._RealCropRect[3] - self._RealCropRect[1]]
		# crop() discards the info dict - copy from original
		info = self._getimage().info.copy()  
		##icc_profile = None
		##if (self._getimage().info.has_key("icc_profile") and
			##len(self._getimage().info["icc_profile"]) > 0):
		##icc_profile = self._getimage().info["icc_profile"]
		if (float(self._getimage().size[0] * self._getimage().size[1]) /
			float(endsize[0] * endsize[1]) >= self.imagecropthreshold):
			# Only crop if >= imagecropthreshold % are outside cropping region
			self.msg("Cropping image...")
			try:
				_image = self._getimage()
				if not imagecopy:
					self._imgASCIIpath = (self._gettmppath() + "." +
										  crc32(self._getimageconf(True,
																   False)) +
										  self._imageextension)
					self._set_imgpath_md5(self._imgASCIIpath)
					imagecopy = True
				self._setimage(_image.crop([self._RealCropRect[0],
											self._RealCropRect[1],
											self._RealCropRect[2],
											self._RealCropRect[3]]))
				# crop() is a lazy operation, call load() to prevent python crash
				self._getimage().load()
				cropped = True
				self._sizemod  = True
				if self.verbose:
					self.msg("Crop rectangle: " + str(self._RealCropRect))
					self.msg("Cropped size: " + str(self._getimage().size[0]) +
							 "x" + str(self._getimage().size[1]))
			except Exception, v:
				self.errorcount += 1
				self.msg("ERROR - fatal error while cropping: " +
						 traceback.format_exc())
				self.msg("Try re-saving the image from your imaging "
						 "application.")
				self._abort()
				return None
		else:
			endsize = intlist(self._getimage().size)
			self._RealCropRect = [0,
								  0,
								  self._getimage().size[0],
								  self._getimage().size[1]]
		if 2.0 in self._version:
			# Assume QuarkXPress
			self._DownsampleDimensions = [int(math.ceil(endsize[0] *
														self._DownsampleFactor[0])),
										  int(math.ceil(endsize[1] *
														self._DownsampleFactor[1]))]
		else:
			self._DownsampleDimensions = [int(round(endsize[0] *
													self._DownsampleFactor[0])),
										  int(round(endsize[1] *
													self._DownsampleFactor[1]))]
		if (self._DownsampleDimensions[0] < endsize[0] or
			self._DownsampleDimensions[1] < endsize[1]):
			self.msg("Downsampling image: %s dpi -> %s dpi..." %
					 ("x".join(str(dpi) for dpi in self._RealRes),
					  "x".join(str(dpi) for dpi in self._DownsampleRes)))
			try:
				_image = self._getimage()
				if not imagecopy:
					self._imgASCIIpath = (self._gettmppath() + "." +
										  crc32(self._getimageconf(True,
																   False)) +
										  self._imageextension)
					self._set_imgpath_md5(self._imgASCIIpath)
					imagecopy = True
				if _image.mode in ("RGB", "RGBA", "CMYK", "CMYKA"):
					DownsampleFilter = self.ColorImageDownsampleFilter
				elif _image.mode in ("L", "LA"):
					DownsampleFilter = self.GrayImageDownsampleFilter
				else:
					DownsampleFilter = self.MonoImageDownsampleFilter
				self._setimage(_image.resize((self._DownsampleDimensions[0],
											  self._DownsampleDimensions[1]),
											 DownsampleFilter))
				self._sizemod  = True
				self._ImageCropFixed = [self._ImageCropFixed[0] *
										self._DownsampleFactor[0],
										self._ImageCropFixed[1] *
										self._DownsampleFactor[1],
										self._ImageCropFixed[2] *
										self._DownsampleFactor[0],
										self._ImageCropFixed[3] *
										self._DownsampleFactor[1]]
				self._ImageCropRect = intlist(self._ImageCropFixed)
				if cropped:
					self._RealCropRect = []
					self._RealCropRect.append(int(math.floor(self._ImageCropFixed[0])))
					self._RealCropRect.append(int(math.floor(self._ImageCropFixed[1])))
					if 2.0 in self._version:
						# Assume QuarkXPress
						self._RealCropRect.append(int(math.ceil(self._ImageCropFixed[2])))
						self._RealCropRect.append(int(math.ceil(self._ImageCropFixed[3])))
					else:
						self._RealCropRect.append(int(math.floor(self._ImageCropFixed[2])))
						self._RealCropRect.append(int(math.floor(self._ImageCropFixed[3])))
						##self._RealCropRect.append(int(round(self._ImageCropFixed[2])))
						##self._RealCropRect.append(int(round(self._ImageCropFixed[3])))
				else:
					self._RealCropRect = [0, 0, self._getimage().size[0], self._getimage().size[1]]
				self._IncludedImageDimensions = intlist(self._getimage().size)
				if self.verbose:
					self.msg("Downsampled size: " +
							 str(self._getimage().size[0]) + "x" +
							 str(self._getimage().size[1]))
			except Exception, v:
				self.errorcount += 1
				self.msg("ERROR - fatal error while downsampling: " +
						 traceback.format_exc())
				self.msg("Try re-saving the image from your imaging "
						 "application.")
				self._abort()
				return None
		self._getimage().info = info
		##if icc_profile != None:
			##self._getimage().info["icc_profile"] = icc_profile
		return self._sizemod 
	
	def _SetRealDimensions(self): # set "real" dimensions in pt
		if self._ImagePosition:
			# Width in pt
			self._RealDimensions.append(max(math.sqrt((self._ImagePosition[0] -
													   self._ImagePosition[6]) ** 2 +
													  (self._ImagePosition[1] -
													   self._ImagePosition[7]) ** 2),
											math.sqrt((self._ImagePosition[2] -
													   self._ImagePosition[4]) ** 2 +
													  (self._ImagePosition[3] -
													   self._ImagePosition[5]) ** 2))) 
			# Height in pt
			self._RealDimensions.append(max(math.sqrt((self._ImagePosition[2] -
													   self._ImagePosition[0]) ** 2 +
													  (self._ImagePosition[3] -
													   self._ImagePosition[1]) ** 2),
											math.sqrt((self._ImagePosition[4] - 
													   self._ImagePosition[6]) ** 2 +
													  (self._ImagePosition[5] -
													   self._ImagePosition[7]) ** 2)))

	def _getseparation(self, name, CMYK):
		return ["%BeginPyOPISeparationProcSet",
		"[/Separation (" + name + ") /DeviceCMYK { dup " + str(CMYK[0]) + " mul",
		"exch " + str(CMYK[1]) + " exch dup " + str(CMYK[2]) + " mul",
		"exch " + str(CMYK[3]) + " mul",
		"}] setcolorspace",
		"%EndPyOPISeparationProcSet"]
	
	def _getdefaultprocset(self):
		return [
			"%BeginPyOPIDefaultProcSet",
			"/B {bind def} bind def",
			"/X {exch def} B",
			"/ImageDict 7 dict def",
			"/CreateImageDict{ImageDict begin /Decode X /DataSource X /ImageMatrix X",
			" /BitsPerComponent X /Height X /Width X /ImageType 1 def end}B",
			"/inkmul{",
			" array astore{1 index mul exch}forall pop",
			"}B",
			"%EndPyOPIDefaultProcSet"
		]
	
	def _getdntocmykf(self):
		# requires /B
		return [
			"/dntocmykf",
			"{",
			" [",
			"  exch dup length 0 0 0 0 4 index 4 add 4 rollL",
			"  9 -2 roll dup 1 sub 3 -1 roll",
			"  {",
			"   3 exch",
			"   {",
			"    dup 0 eq",
			"    {",
			"     pop",
			"    }",
			"    {",
			"     dup 1 eq",
			"     {",
			"      pop 1 index indexL 2 index 5 index add 2 add -1 rollL",
			"      addL 6 index 9 index add 1 add 1 rollL 12 -3 roll",
			"     }",
			"     {",
			"      2 index 1 add indexL mulL 4 index 7 index add 2 add -1 rollL",
			"      addL 8 index 11 index add 1 add 1 rollL 14 -3 roll",
			"     } ifelse",
			"    } ifelse",
			"    1 sub",
			"   } forall pop 1 sub",
			"  } forall pop {popL} repeat",
			"  4 {dupL 1 gtL {pop 1} ifL 4 1 rollL} repeat",
			" ] cvx bind",
			"} B"
		]
	
	def _getgendn(self):
		# requires /dntocmykf
		return [
			"/gendn{",
			" dup length 3 1 roll mark 3 index 5 add 3 roll",
			" inkmul counttomark 3 add -3 roll pop llge3orseps",
			" {",
			"  [/DeviceN 3 -1 roll /DeviceCMYK 5 -1 roll dntocmykf]",
			"  setcolorspace setcolor",
			" }",
			" {pop dntocmykf exec C} ifelse",
			"} B"
		]
	
	def _getgendncs(self):
		return [
			"/gendncs",
			"{",
			" [/DeviceN 3 -1 roll/DeviceCMYK 5 -1 roll dntocmykf]",
			"} B"
		]
	
	def _getllge2(self):
		return [
			"/llge2 /languagelevel where {pop languagelevel}{1} ifelse 2 ge def"
		]
	
	def _getllge3(self):
		return [
			"/llge3 /languagelevel where {pop languagelevel}{1} ifelse 3 ge def",
			"/llge3orseps where {pop}{/llge3orseps llge3 def} ifelse"
		]
	
	def _hasdevicenprocset(self):
		pyopidevicenprocset = re.compile("(?:^|\s)(%BeginPyOPIDeviceNProcSet\s+.+?\s+%EndPyOPIDeviceNProcSet)(?:$|\s)",
										 re.I | re.S)
		if pyopidevicenprocset.search("\n".join(self._gfxstate)) == None:
			qxpllge3orseps = re.search("(?:^|\s)(llge3orseps\s*{.+?}\s*{.+?}\s*ifelse)(?:$|\s)",
									   "\n".join(self._gfxstate), re.I | re.S)
			if qxpllge3orseps == None:
				return False
		return True
	
	def _hastransformationmatrix(self):
		return "/tempmatrix matrix currentmatrix def" in self._gfxstate
	
	def _is_cached(self, imagepath):
		return self._is_mem_cached(imagepath) or self._is_disk_cached(imagepath)
	
	def _is_mem_cached(self, imagepath):
		idx = md5(imagepath).hexdigest()
		return self._imagecache.has_key(idx)
	
	def _is_disk_cached(self, imagepath):
		return path.exists(imagepath) and path.isfile(imagepath) ##and os.stat(imagepath).st_size > 0  # symlinks are size 0!
	
	def _is_same_age(self, imagepath):
		return int(os.stat(imagepath).st_mtime) == int(os.stat(self._imgASCIIpath).st_mtime)
	
	def _set_imgpath_md5(self, imagepath):
		self._imgpath_md5 = md5(imagepath).hexdigest()
	
	def _inc_occurrences(self):
		self._imagecache[self._imgpath_md5]["occurrences"] += 1
		if (not len(self._max_occurrences) or
			self._max_occurrences[-1] <
			self._imagecache[self._imgpath_md5]["occurrences"]):
			self._max_occurrences.append(self._imagecache[self._imgpath_md5]["occurrences"])
	
	def _checkpurgecache(self, bytes):
		if self.usecache and self._imageformat != "[internal]":
			if self._cachebytes + bytes > self.cachemegs * 1024 * 1024:
				self.msg("Requested memory cache size exceeding " +
						 str(self.cachemegs) + " MB (actual cache size " +
						 str(round(self._cachebytes / 1024.0 / 1024.0, 2)) +
						 " MB, requested size " +
						 str(round((self._cachebytes + bytes) / 1024.0 / 1024.0,
								   2)) + " MB). Purging memory cache...")
				self._purgecache(bytes, 0)
		else:
			# clear cache entry
			self._delimage()
			if len(self._max_occurrences): self._max_occurrences.pop()
	
	def _purgecache(self, bytes, occurrences):
		if not occurrences and len(self._max_occurrences):
			occurrences = self._max_occurrences[-1]
		else:
			occurrences = 1
		trash = []
		for img in self._imagecache:
			if self._cachebytes + bytes <= self.cachemegs * 1024 * 1024:
				break
			if occurrences == 1 or self._imagecache[img]["occurrences"] < occurrences:
				self._cachebytes -= self._imagecache[img]["bytes"]
				self.msg("Purging " +
						 str(round(self._imagecache[img]["bytes"] / 1024.0 / 1024.0,
								   2)) + " MB. New cache size: " +
						 str(round(self._cachebytes / 1024.0 / 1024.0, 2)) +
						 " MB")
				trash.append(img)
		for img in trash:
			del self._imagecache[img]
			if len(self._max_occurrences):
				self._max_occurrences.pop()
			if len(self._max_occurrences):
				occurrences = self._max_occurrences[-1]
		if (self._cachebytes + bytes > self.cachemegs * 1024 * 1024 and
			len(self._imagecache)):
			self._purgecache(bytes, occurrences + 1)
	
	def _setimage(self, image):
		if image.mode:
			if image.mode == "1":
				bpp = 1
			else:
				bpp = 8
			bytes = (image.size[0] * image.size[1] * len(image.mode) * bpp) / 8
		else:
			bytes = len(image.data)
		self._checkpurgecache(bytes)
		if self._imagecache.has_key(self._imgpath_md5):
			self._cachebytes -= self._imagecache[self._imgpath_md5]["bytes"]
			self._imagecache[self._imgpath_md5]["image"] = image
			self._imagecache[self._imgpath_md5]["bytes"] = bytes
		else:
			self._imagecache[self._imgpath_md5] = {"image": image,
												   "bytes": bytes,
												   "occurrences": 0,
												   "path": self._imgASCIIpath}
		self._cachebytes += bytes
	
	def _getimage(self):
		return self._imagecache[self._imgpath_md5]["image"]
	
	def _delimage(self, key = None):
		if key == None:
			key = self._imgpath_md5
		if self._imagecache.has_key(key):
			self._cachebytes -= self._imagecache[key]["bytes"]
			del self._imagecache[key]

	def _write(self):
		self._SetRealDimensions()
		
		# Open the image
		if self.usecache or self.usediskcache: # use cached file if recent
			tmppath = (self._gettmppath() + "." +
					   crc32(self._getimageconf(True, True)) +
					   self._imageextension)
			if self._is_cached(tmppath):
				if (self._is_mem_cached(tmppath) or
					self._is_same_age(tmppath)):
					# Recent version in cache
					self._sizemod = True
					self._colormod = True
			else:
				tmppath = (self._gettmppath() + "." +
						   crc32(self._getimageconf(True, False)) +
						   self._imageextension)
				if self._is_cached(tmppath):
					if (self._is_mem_cached(tmppath) or
						self._is_same_age(tmppath)):
						# Recent version in cache
						self._sizemod = True
				else:
					tmppath = (self._gettmppath() + "." +
							   crc32(self._getimageconf(False, True)) +
							   self._imageextension)
					if self._is_cached(tmppath):
						if (self._is_mem_cached(tmppath) or
							self._is_same_age(tmppath)):
							# Recent version in cache
							self._colormod = True
					else:
						tmppath = (self._gettmppath() + "." +
								   crc32(self._getimageconf(False, False)) +
								   self._imageextension)
						if not self._is_cached(tmppath):
							tmppath = self._gettmppath()
			
			if tmppath != self._imgASCIIpath and self._is_cached(tmppath):
				if self._is_mem_cached(tmppath) or self._is_same_age(tmppath):
					# Recent version in cache
					self._imagecached = True
					self.msg("Image already in cache")
					self._imgASCIIpath = tmppath
				else:
					self.msg("Cached image is not same age as original.")
					self.msg("Original image (" +
							 path.basename(self._ImageFileName) +
							 ") age in seconds: " +
							 str(int(os.stat(self._imgASCIIpath).st_mtime)))
					self.msg("Cached image (" + path.basename(tmppath) +
							 ") age in seconds: " +
							 str(int(os.stat(tmppath).st_mtime)))
		self._set_imgpath_md5(self._imgASCIIpath)
		if not self._is_mem_cached(self._imgASCIIpath):
			try:
				if self._is_disk_cached(self._imgASCIIpath):
					if self._aborted:
						self._reset()
						return
					if self._imageformat != "epsf":
						if self.verbose:
							self.msg("Opening: " +self._imgASCIIpath)
						self._setimage(Image.open(self._imgASCIIpath))
						if self._getimage().mode not in ("1",
														 "L",
														 "RGB",
														 "CMYK"):
							self._errorstr = ("ERROR - unsupported mode: " +
											  self._getimage().mode)
							if self.abortonerror:
								self.errorcount += 1
								self.msg(self._errorstr)
								self._abort()
								return
					else:
						self._setimage(EPSImage(self._imgASCIIpath))
				else:
					self._errorstr = ("ERROR - image file not found: " +
									  self._ImageFileName)
					if self.abortonfilenotfound:
						self.errorcount += 1
						self.msg(self._errorstr)
						self._abort()
						return
			except IOError, v:
				self._errorstr = ("ERROR - could not read image file: " +
								  self._ImageFileName)
		else:
			self.msg("Image already in memory")
		
		if self._errorstr:
			self.errorcount += 1
			if self.abortonerror:
				self.msg(self._errorstr)
				self._abort()
			else:
				self._setimage(self._failimage(self._errorstr))
				self._imageformat = "[internal]"
		
		if self._aborted:
			self._reset()
			return
		
		# PROCESS IMAGE (Crop / Downsample / Color Convert)
		if self.verbose:
			self.msg("Type: " + self._imageformat)
		if self._imageformat != "epsf":
			if self._getimage().info.has_key("dpi"):
				self._ImageResolution = self._getimage().info["dpi"]
			elif self._getimage().info.has_key("dpc"):
				self._ImageResolution = (self._getimage().info["dpc"][0] * 2.54,
										 self._getimage().info["dpc"][1] * 2.54)
			ImageDimensions = (self._ImageDimensions[0],
							   self._ImageDimensions[1])
			self.msg("Mode: " + self._getimage().mode)
			if self.verbose:
				self.msg("Size: " + str(self._getimage().size[0]) + "x" +
						 str(self._getimage().size[1]))
			self._DownsampleDimensions = [self._getimage().size[0],
										  self._getimage().size[1]]
			self._ImageDimensions = [self._getimage().size[0],
									 self._getimage().size[1]]
			self._IncludedImageDimensions = [self._getimage().size[0],
											 self._getimage().size[1]]
			
			if not self._errorstr:
				if self._imagecached and self._sizemod:
					if self._ImageCropFixed:
						cropped = False
						if (float(ImageDimensions[0] * ImageDimensions[1]) /
							((self._ImageCropFixed[2] - self._ImageCropFixed[0]) *
							 (self._ImageCropFixed[3] - self._ImageCropFixed[1])) >=
							self.imagecropthreshold):
							cropped = True
							if 2.0 in self._version:
								# Assume QuarkXPress
								size = [math.ceil(self._ImageCropFixed[2]) -
												  math.floor(self._ImageCropFixed[0]),
										math.ceil(self._ImageCropFixed[3]) -
												  math.floor(self._ImageCropFixed[1])]
							else:
								size = [math.floor(self._ImageCropFixed[2]) -
										math.floor(self._ImageCropFixed[0]),
										math.floor(self._ImageCropFixed[3]) -
										math.floor(self._ImageCropFixed[1])]
								##size = [round(self._ImageCropFixed[2]) -
											  ##math.floor(self._ImageCropFixed[0]),
										##round(self._ImageCropFixed[3]) -
											  ##math.floor(self._ImageCropFixed[1])]
						else:
							size = ImageDimensions
						self._DownsampleFactor = [float(self._getimage().size[0]) /
												  size[0],
												  float(self._getimage().size[1]) /
												  size[1]]
						self._ImageCropFixed = _ImageCropFixed = [self._ImageCropFixed[0] *
																  self._DownsampleFactor[0],
																  self._ImageCropFixed[1] *
																  self._DownsampleFactor[1],
																  self._ImageCropFixed[2] *
																  self._DownsampleFactor[0],
																  self._ImageCropFixed[3] *
																  self._DownsampleFactor[1]]
						self._ImageCropRect = intlist(self._ImageCropFixed)
						if cropped:
							self._RealCropRect = []
							self._RealCropRect.append(int(math.floor(self._ImageCropFixed[0])))
							self._RealCropRect.append(int(math.floor(self._ImageCropFixed[1])))
							if 2.0 in self._version:
								# Assume QuarkXPress
								self._RealCropRect.append(int(math.ceil(self._ImageCropFixed[2])))
								self._RealCropRect.append(int(math.ceil(self._ImageCropFixed[3])))
							else:
								self._RealCropRect.append(int(math.floor(self._ImageCropFixed[2])))
								self._RealCropRect.append(int(math.floor(self._ImageCropFixed[3])))
								##self._RealCropRect.append(int(round(self._ImageCropFixed[2])))
								##self._RealCropRect.append(int(round(self._ImageCropFixed[3])))
						else:
							self._RealCropRect = [0,
												  0,
												  self._getimage().size[0],
												  self._getimage().size[1]]
					else:
						self._RealCropRect = _ImageCropFixed = [0,
																0,
																self._getimage().size[0],
																self._getimage().size[1]]
				else:
					if self._ImageCropFixed:
						_ImageCropFixed = []
						_ImageCropFixed.append((float(self._getimage().size[0]) /
												ImageDimensions[0]) *
											   self._ImageCropFixed[0])
						_ImageCropFixed.append((float(self._getimage().size[1]) /
												ImageDimensions[1]) *
											   self._ImageCropFixed[1])
						_ImageCropFixed.append((float(self._getimage().size[0]) /
												ImageDimensions[0]) *
											   self._ImageCropFixed[2])
						_ImageCropFixed.append((float(self._getimage().size[1]) /
												ImageDimensions[1]) *
											   self._ImageCropFixed[3])
						self._ImageCropFixed = _ImageCropFixed
						self._ImageCropRect = intlist(_ImageCropFixed)
						self._RealCropRect.append(int(math.floor(_ImageCropFixed[0])))
						self._RealCropRect.append(int(math.floor(_ImageCropFixed[1])))
						if 2.0 in self._version:
							# Assume QuarkXPress
							self._RealCropRect.append(int(math.ceil(_ImageCropFixed[2])))
							self._RealCropRect.append(int(math.ceil(_ImageCropFixed[3])))
							size = [math.ceil(self._ImageCropFixed[2]) -
									math.floor(self._ImageCropFixed[0]),
									math.ceil(self._ImageCropFixed[3]) -
									math.floor(self._ImageCropFixed[1])]
							self.msg("Adjusting crop for QuarkXPress...")
							if ImageDimensions[0] != size[0]:
								if math.floor(self._ImageCropFixed[0]) != 0:
									self.msg("Adjusting X1 - 1")
									self._RealCropRect[0] -= 1
								if (math.ceil(self._ImageCropFixed[2]) !=
									ImageDimensions[0]):
									self.msg("Adjusting X2 + 1")
									self._RealCropRect[2] += 1
							if ImageDimensions[1] != size[1]:
								if math.floor(self._ImageCropFixed[1]) != 0:
									self.msg("Adjusting Y1 - 1")
									self._RealCropRect[1] -= 1
								if (math.ceil(self._ImageCropFixed[3]) !=
									ImageDimensions[1]):
									self.msg("Adjusting Y2 + 1")
									self._RealCropRect[3] += 1
						else:
							self._RealCropRect.append(int(math.floor(_ImageCropFixed[2])))
							self._RealCropRect.append(int(math.floor(_ImageCropFixed[3])))
							##self._RealCropRect.append(int(round(_ImageCropFixed[2])))
							##self._RealCropRect.append(int(round(_ImageCropFixed[3])))
							##self._RealCropRect.append(int(math.ceil(_ImageCropFixed[2])))
							##self._RealCropRect.append(int(math.ceil(_ImageCropFixed[3])))
					else:
						self._RealCropRect = _ImageCropFixed = [0,
																0,
																self._getimage().size[0],
																self._getimage().size[1]]
				if self._RealDimensions and _ImageCropFixed:
					# X-resolution (dpi)
					self._RealRes.append(float(_ImageCropFixed[2] -
											   _ImageCropFixed[0]) /
										 (self._RealDimensions[0] / 72.0))
					# Y-resolution (dpi)
					self._RealRes.append(float(_ImageCropFixed[3] -
											   _ImageCropFixed[1]) /
										 (self._RealDimensions[1] / 72.0))
					stdres = {"1": self.MonoImageResolution,
							  "L": self.GrayImageResolution,
							  "RGB": self.ColorImageResolution,
							  "CMYK": self.ColorImageResolution}
					minres = {"1": self.MonoImageMinResolution,
							  "L": self.GrayImageMinResolution,
							  "RGB": self.ColorImageMinResolution,
							  "CMYK": self.ColorImageMinResolution}
					if (min(self._RealRes[0], self._RealRes[1]) >=
						stdres[self._getimage().mode]):
						self._IncludedImageQuality = 3.0
					elif (min(self._RealRes[0], self._RealRes[1]) >=
						  minres[self._getimage().mode]):
						self._IncludedImageQuality = 2.0
				if not self._imagecached:
					self._detectcmykgrayimages()
					self._SetDownsampleDimensions()
					if not self._sizemod and self._CropAndDownsample() == None:
						# Exception
						return
					self._ICCtransform()
					if self._aborted:
						self._reset()
						return
				elif not self._sizemod:
					self._SetDownsampleDimensions()
					if self._CropAndDownsample() == None:
						# Exception
						return
			
			if 1.3 in self.version and not self._ImageCropRect:
				self._ImageCropRect = self._ImageCropFixed = (0,
															  0,
															  self._getimage().size[0],
															  self._getimage().size[1])
			
			channels = len(self._getimage().mode)
			
			_mode = self.mode.lower()[0]
			try:
				if _mode == "b":
					if self.verbose: self.msg("Getting image data as binary...")
					imagedata = self._getimage().tostring()
				else:
					if self.verbose: self.msg("Getting image data as hex...")
					imagedata = binascii.hexlify(self._getimage().tostring())
			except Exception, v:
				self.errorcount += 1
				self.msg("ERROR - fatal error while reading image: " +
						 traceback.format_exc())
				self.msg("Try re-saving the image from your imaging application.")
				self._abort()
				return
			
			bytes = len(imagedata)
			if self.verbose: self.msg("Size (bytes): " + str(bytes))
			bpp = (bytes * 8) / (self._getimage().size[0] *
								 self._getimage().size[1] * channels)
			if _mode == "a":
				bpp = bpp / 2
			if self.verbose: self.msg("BPP: " + str(bpp))
		else:
			# EPSF
			self._IncludedImageQuality = 2.0
			imagedata = self._getimage().data
			
		self._inc_occurrences()
		
		if self._imageformat != "epsf":
			##if ((self._getimage().mode == "1" and self._ImageType and
				 ##len(self._ImageType) > 1 and self._ImageType[1] > 1) or
			    ##self._getimage().mode == "L"):
			if self._getimage().mode in ("1", "L"):
				if (not (self._ImageColor or self._ImageInks) or
					self._ImageInks == "full_color"):
					self._ImageColorType = "Process"
					self._ImageColor = [0, 0, 0, 1, "Black"]
					self._ImageTint = 1.0
					self._ImageInks = "monochrome 1 (Black) 1.0"
		
		if 1.3 in self.version:
			if self.verbose:
				self.msg("Inserting OPI 1.3 comments...")
			self._raw_write("%ALDImageFileName: " + self.escapefilename() +
							self.newline)
			if self._ImageID:
				self._raw_write("%ALDImageID: " + self.escapefilename() +
								self.newline)
			if self._ObjectComments:
				self._raw_write("%ALDObjectComments: " + self._ObjectComments +
								self.newline)
			self._raw_write("%ALDImageDimensions: " +
							str(int(self._ImageDimensions[0])) + " " +
							str(int(self._ImageDimensions[1])) + self.newline)
			self._raw_write("%ALDImageCropRect: " +
							str(self._ImageCropRect[0]) + " " +
							str(self._ImageCropRect[1]) + " " +
							str(self._ImageCropRect[2]) + " " +
							str(self._ImageCropRect[3]) + self.newline)
			if self._ImageCropFixed:
				self._raw_write("%ALDImageCropFixed: " +
								str(Decimal(str(self._ImageCropFixed[0]))) + " " +
								str(Decimal(str(self._ImageCropFixed[1]))) + " " +
								str(Decimal(str(self._ImageCropFixed[2]))) + " " +
								str(Decimal(str(self._ImageCropFixed[3]))) +
								self.newline)
			self._raw_write("%ALDImagePosition: " +
							" ".join(strlist(self._ImagePosition)) +
							self.newline)
			if len(self._ImageResolution):
				self._raw_write("%ALDImageResolution: " +
								" ".join(strlist(self._ImageResolution)) +
								self.newline)
			if self._ImageColorType:
				self._raw_write("%ALDImageColorType: " +
								self._ImageColorType + self.newline)
			if self._ImageColor:
				self._raw_write("%ALDImageColor: " +
								" ".join(strlist(self._ImageColor[0:4])) +
								" (" + self._ImageColor[4] + ")" + self.newline)
			if self._ImageTint:
				self._raw_write("%ALDImageTint: " + str(self._ImageTint) +
								self.newline)
			if self._ImageOverprint == False:
				self._raw_write("%ALDImageOverprint: false" + self.newline)
			if self._ImageOverprint == True:
				self._raw_write("%ALDImageOverprint: true" + self.newline)
			if self._ImageType:
				self._raw_write("%ALDImageType: " + str(channels) + " " +
								str(bpp) + self.newline)
			if len(self._ImageGrayMap):
				for n, item in enumerate(self._ImageGrayMap):
					if n == 0:
						self._raw_write("%ALDImageGrayMap: " +
										" ".join(strlist(item)) + self.newline)
					else:
						self._raw_write("%%+ " + " ".join(strlist(item)) +
										self.newline)
			if self._ImageTransparency == False:
				self._raw_write("%ALDImageTransparency: false" + self.newline)
			if self._ImageTransparency == True:
				self._raw_write("%ALDImageTransparency: true" + self.newline)
			if len(self._TIFFASCIITags):
				for tag in self._TIFFASCIITags:
					self._raw_write("%ALDImageAsciiTag" + tag + ": ")
					for n, item in enumerate(self._TIFFASCIITags[tag]):
						if n == 0:
							self._raw_write(item + self.newline)
						else:
							self._raw_write("%%+ " + item + self.newline)
			self._raw_write("%%BeginObject: image" + self.newline)

		if 2.0 in self.version:
			if self.verbose: self.msg("Inserting OPI 2.0 comments...")
			self._raw_write("%%BeginOPI: 2.0" + self.newline)
			self._raw_write("%%ImageFileName: " + self.escapefilename() +
							self.newline)
			if self._MainImage:
				self._raw_write("%%MainImage: " + self.escapefilename() +
								self.newline)
			if len(self._TIFFASCIITags):
				for tag in self._TIFFASCIITags:
					self._raw_write("%%TIFFASCIITag: " + tag + " ")
					for n, item in enumerate(self._TIFFASCIITags[tag]):
						if n == 0:
							self._raw_write("(" + item + ")" + self.newline)
						else:
							self._raw_write("%%+ (" + item + ")" + self.newline)
			if self._ImageDimensions and self._ImageCropFixed:
				self._raw_write("%%ImageDimensions: " +
								str(self._ImageDimensions[0]) + " " +
								str(self._ImageDimensions[1]) + self.newline)
				self._raw_write("%%ImageCropRect: " +
								str(Decimal(str(self._ImageCropFixed[0]))) + " " +
								str(Decimal(str(self._ImageCropFixed[1]))) + " " +
								str(Decimal(str(self._ImageCropFixed[2]))) + " " +
								str(Decimal(str(self._ImageCropFixed[3]))) +
								self.newline)
			if self._ImageOverprint == False:
				self._raw_write("%%ImageOverprint: false" + self.newline)
			if self._ImageOverprint == True:
				self._raw_write("%%ImageOverprint: true" + self.newline)
			if self._ImageInks:
				self._raw_write("%%ImageInks: " + self._ImageInks +
								self.newline)
			elif self._ImageColor:
				self._raw_write("%%ImageInks: ")
				if channels == 1:
					inks = ""
					if (not self._ImageColor[4] or self._ImageColor[4] in
						("Cyan", "Magenta", "Yellow", "Black") or
						(self._ImageColorType and self._ImageColorType.lower() == "process")):
						n = 0
						if self._ImageColor[0] > 0:
							n = n + 1
							inks = (inks + " (Cyan) " +
									str(self._ImageColor[0] *
										(self._ImageTint or 1.0)))
						if self._ImageColor[1] > 0:
							n = n + 1
							inks = (inks + " (Magenta) " +
									str(self._ImageColor[1] *
										(self._ImageTint or 1.0)))
						if self._ImageColor[2] > 0:
							n = n + 1
							inks = (inks + " (Yellow) " +
									str(self._ImageColor[2] *
										(self._ImageTint or 1.0)))
						if self._ImageColor[3] > 0:
							n = n + 1
							inks = (inks + " (Black) " +
									str(self._ImageColor[3] *
										(self._ImageTint or 1.0)))
					else:
						n = 1
						if self._ImageTint != None:
							tint = self._ImageTint
						else:
							tint = 1.0
						inks = " (" + self._ImageColor[4] + ") " + str(tint)
					self._raw_write("monochrome " + str(n) + inks)
				else:
					self._raw_write("full_color")
				self._raw_write(self.newline)
		
		if self._imageformat != "epsf":
		
			self.msg("Setting up the graphics state...")
			self._gfxstate += self._getdefaultprocset()
			
			##if self._ImageOverprint == False:
				##self._raw_write("false setoverprint" + self.newline)
			##elif self._ImageOverprint == True:
				##self._raw_write("true setoverprint" + self.newline)
			
			if self._getimage().mode == "1": ##and self._ImageType and len(self._ImageType) > 1 and self._ImageType[1] > 1:
				# FPO is a grayscale image, so we need to set the color for the
				# bitmap
				self.msg("Setting up 1-bit image colorization postscript code...")
				self._gfxstate.append("%BeginPyOPIColorProcSet")
				if (self._ImageColorType and
					self._ImageColorType.lower() == "process"):
					self._gfxstate.append("/C/setcmykcolor load def")
					for i in xrange(4):
						self._gfxstate.append(str(self._ImageColor[i] *
												  (self._ImageTint or 1.0)) +
											  " ")
					self._gfxstate.append("C")
				elif not self._hasdevicenprocset():
					self._gfxstate.append("%BeginPyOPIDeviceNProcSet")
					self._gfxstate += self._getllge2()
					self._gfxstate += self._getllge3()
					self._gfxstate.append("llge2")
					self._gfxstate.append("{")
					self._gfxstate.append(" /scs where {pop}{/scs /setcolorspace load def} ifelse")
					self._gfxstate.append(" /sc where {pop}{/sc /setcolor load def} ifelse")
					self._gfxstate.append(" /dupL {/dup load} B")
					self._gfxstate.append(" /mulL {/mul load} B")
					self._gfxstate.append(" /rollL {/roll load} B")
					self._gfxstate.append(" /indexL {/index load} B")
					self._gfxstate.append(" /addL {/add load} B")
					self._gfxstate.append(" /popL {/pop load} B")
					self._gfxstate.append(" /gtL {/gt load} B")
					self._gfxstate.append(" /ifL {/if load} B")
					self._gfxstate.append("} if")
					self._gfxstate += self._getdntocmykf()
					self._gfxstate += self._getgendn()
					
					self._gfxstate.append(str(self._ImageTint or 1.0) +
										  " 1 [[" +
										  " ".join(strlist(self._ImageColor[0:4])) +
										  " ]][(" + self._ImageColor[4] + ")]gendn")
					# 1 1 [[0 0 1 0 ]][(Spot Color Name)]gendn
					# GlobalTint ColorTint [[C M Y K]]
					
					self._gfxstate.append("%EndPyOPIDeviceNProcSet")
				self._gfxstate.append("%EndPyOPIColorProcSet")
			
			elif (self._getimage().mode == "L" and
				  not self._hasdevicenprocset() and
				  self._ImageColor[0:4] != [0, 0, 0, 1]):
				self._gfxstate.append("%BeginPyOPIColorProcSet")
				if True:
					self.msg("Setting up grayscale image colorization postscript code...")
					self._gfxstate.append("%BeginPyOPIDeviceNProcSet")
					self._gfxstate += self._getllge2()
					self._gfxstate += self._getllge3()
					self._gfxstate.append("llge2")
					self._gfxstate.append("{")
					self._gfxstate.append(" /scs where {pop}{/scs /setcolorspace load def} ifelse")
					self._gfxstate.append(" /sc where {pop}{/sc /setcolor load def} ifelse")
					self._gfxstate.append(" /dupL {/dup load} B")
					self._gfxstate.append(" /mulL {/mul load} B")
					self._gfxstate.append(" /rollL {/roll load} B")
					self._gfxstate.append(" /indexL {/index load} B")
					self._gfxstate.append(" /addL {/add load} B")
					self._gfxstate.append(" /popL {/pop load} B")
					self._gfxstate.append(" /gtL {/gt load} B")
					self._gfxstate.append(" /ifL {/if load} B")
					self._gfxstate.append("} if")
					self._gfxstate += self._getdntocmykf()
					self._gfxstate += self._getgendncs()
					#
					self._gfxstate.append("llge3orseps{")
					str_ = "[/Indexed ["
					colors = []
					bgcolors = {}
					inknames = ["Cyan", "Magenta", "Yellow", "Black", "Gelb",
								"Schwarz"]
					if self._ImageInks and self._ImageInks != "full_color":
						inks = self._ImageInks.split("(")[1:]
						if not inks:
							colors.append([0, [1, 0, 0, 0], "Cyan", 0, 255])
							colors.append([0, [0, 1, 0, 0], "Magenta", 0, 255])
							colors.append([0, [0, 0, 1, 0], "Yellow", 0, 255])
							colors.append([0, [0, 0, 0, 1], "Black", 0, 255])
						else:
							for ink in inks:
								ink = ink.split(")", 1)
								ink[1] = float(ink[1])
								if ink[0] in inknames:
									for i in xrange(len(inknames)):
										if ink[0] == inknames[i]:
											if i > 3:
												i -= 2
											ink[0] = inknames[i]
											color = [0, 0, 0, 0]
											color[i] = 1
											break
									colors.append([ink[1],
												   color,
												   ink[0], 0, 255])
									if self.verbose:
										self.msg("Ink: " + str(colors[-1]))
								elif ink[0] in self._spotcolors:
									colors.append([ink[1],
												   self._spotcolors[ink[0]],
												   ink[0], 0, 255])
									if self.verbose:
										self.msg("Ink: " + str(colors[-1]))
								elif self._ImageColor:
									colors.append([ink[1],
												   self._ImageColor[0:4],
												   ink[0], 0, 255])
									if self.verbose:
										self.msg("Ink: " + str(colors[-1]))
					elif self._ImageColor:
						if (self._ImageColorType and
							self._ImageColorType.lower() == "process" and
							self._ImageColor[0:4] != [0.0, 0.0, 0.0, 0.0]):
							for i, ink in enumerate(self._ImageColor[0:4]):
								if ink > 0:
									color = [0, 0, 0, 0]
									color[i] = 1
									colors.append([(self._ImageTint or 1.0) *
												   ink,
												   color,
												   inknames[i], 0, 255])
						else:
							colors.append([self._ImageTint or 1.0,
										   self._ImageColor[0:4],
										   self._ImageColor[4], 0, 255])
					if self._bgcolor:
						for n in self._bgcolor:
							colors.append([n[0], n[1], n[2], 0, 255])
							bgcolors[n[2]] = [n[0], n[1], n[2], 0, 255]
					
					for color in colors:
						str_ += "[" + " ".join(strlist(color[1])) + "]"
					str_ += "]["
					for color in colors:
						str_ += "(" + color[2] + ")"
					self._gfxstate.append(str_ + "] gendncs")
					str_ = "255 <"
					
					for i, color in enumerate(colors):
						colors[i][3] = []
						for j in xrange(256):
							# 0...255, 256 steps
							colors[i][3].append(j)
					
					for s in xrange(256):
						for i, color in enumerate(colors):
							i += 1
							n = color[3][s]
							if (len(colors) > 1 and self._bgcolor and
								i > len(colors) - len(self._bgcolor)):
								# Background color
								str_ += hex(int(round((255 - n) *
													  color[0]))).replace("0x",
																		  "").rjust(2,
																					"0")
							else:
								# Image color
								str_ += hex(int(round(n *
													  color[0]))).replace("0x",
																		  "").rjust(2,
																					"0")
						str_ += " "
					self._gfxstate.append(str_ + ">")
					self._gfxstate.append("] setcolorspace")
					self._gfxstate.append("}{")
					self._gfxstate.append("[/Indexed /DeviceCMYK")
					str_ = "255 <"
					for s in xrange(256):
						cmyk = [0, 0, 0, 0]
						for i, color in enumerate(colors):
							i += 1
							n = color[3][s]
							for j, ink in enumerate(color[1]):
								if (len(colors) > 1 and self._bgcolor and
									i > len(colors) - len(self._bgcolor)):
									# Background color
									ink = int(round((255 - n) * color[0] * ink))
								else:
									# Image color
									ink = int(round(n * color[0] * ink))
								if ink > cmyk[j]: cmyk[j] = ink
						for color in cmyk:
							str_ += hex(color).replace("0x", "").rjust(2, "0")
					self._gfxstate.append(str_ + " >")
					self._gfxstate.append("] setcolorspace")
					self._gfxstate.append("}ifelse")
					self._gfxstate.append("%EndPyOPIDeviceNProcSet")
				self._gfxstate.append("%EndPyOPIColorProcSet")
			
			if 2.0 in self._version: ##self._hastransformationmatrix():
				self.msg("Using preset transformation matrix")
			elif self._ImagePosition:
				# If detected OPI version is 1.3 or gfxstate is empty, setup
				# transformation matrix
				w = self._getimage().size[0]
				h = self._getimage().size[1]
				llx = self._ImagePosition[0]
				lly = self._ImagePosition[1]
				ulx = self._ImagePosition[2]
				uly = self._ImagePosition[3]
				urx = self._ImagePosition[4]
				ury = self._ImagePosition[5]
				lrx = self._ImagePosition[6]
				lry = self._ImagePosition[7]
				a = Decimal(str((lrx - llx) / w))
				b = Decimal(str((lry - lly) / w))
				c = Decimal(str((ulx - llx) / h))
				d = Decimal(str((uly - lly) / h))
				tx = Decimal(str(llx))
				ty = Decimal(str(lly))
				# Reset any preset transformation matrix to device defaults
				self._gfxstate.append("initmatrix")
				self._gfxstate.append("[" + str(a) + " " + str(b) + " " +
									  str(c) + " " + str(d) + " " + str(tx) +
									  " " + str(ty) + "] concat")
				self._gfxstate.append("[" + str(w) + " 0 0 " + str(h) +
									  " 0 0] concat")
				if 2.0 in self._version:
					# Assume QuarkXPress
					if self._ImageCropFixed and (self._ImageCropFixed[0] >
												 self._RealCropRect[0] or
												 self._ImageCropFixed[1] >
												 self._RealCropRect[1] or
												 w > self._ImageCropFixed[2] or
												 h > self._ImageCropFixed[3]):
						a = Decimal(str(w / (self._ImageCropFixed[2] -
											 self._ImageCropFixed[0])))
						d = Decimal(str(h / (self._ImageCropFixed[3] -
											 self._ImageCropFixed[1])))
						_ImageCropFixed = [self._ImageCropFixed[0] -
										   self._RealCropRect[0],
										   self._ImageCropFixed[1] -
										   self._RealCropRect[1]]
						_ImageCropFixed.append(_ImageCropFixed[0] +
											   (self._ImageCropFixed[2] -
											    self._ImageCropFixed[0]))
						_ImageCropFixed.append(_ImageCropFixed[1] +
											   (self._ImageCropFixed[3] -
											    self._ImageCropFixed[1]))
						e = Decimal(str(- _ImageCropFixed[0] /
										(_ImageCropFixed[2] -
										 _ImageCropFixed[0])))
						f = Decimal(str(- (h - _ImageCropFixed[3]) /
										(_ImageCropFixed[3] -
										 _ImageCropFixed[1])))
						self._gfxstate.append("[" + str(a) + " 0 0 " + str(d) +
											  " " + str(e) + " " + str(f) +
											  "] concat")
				else:
					if (self._ImageCropRect and (self._ImageCropRect[0] >
												 self._RealCropRect[0] or
												 self._ImageCropRect[1] >
												 self._RealCropRect[1] or
												 w > self._ImageCropRect[2] or
												 h > self._ImageCropRect[3])):
						a = Decimal(str(w / float(self._ImageCropRect[2] -
												  self._ImageCropRect[0])))
						d = Decimal(str(h / float(self._ImageCropRect[3] -
												  self._ImageCropRect[1])))
						_ImageCropRect = [self._ImageCropRect[0] -
										  self._RealCropRect[0],
										  self._ImageCropRect[1] -
										  self._RealCropRect[1]]
						_ImageCropRect.append(_ImageCropRect[0] +
											  (self._ImageCropRect[2] -
											   self._ImageCropRect[0]))
						_ImageCropRect.append(_ImageCropRect[1] +
											  (self._ImageCropRect[3] -
											   self._ImageCropRect[1]))
						e = Decimal(str(- _ImageCropRect[0] /
										float(_ImageCropRect[2] -
											  _ImageCropRect[0])))
						f = Decimal(str(- (h - _ImageCropRect[3]) /
										float(_ImageCropRect[3] -
											  _ImageCropRect[1])))
						self._gfxstate.append("[" + str(a) + " 0 0 " + str(d) +
											  " " + str(e) + " " + str(f) +
											  "] concat")
				# [w skewv skewh h movex movey]
			else:
				self.msg("WARNING: Could not determine or setup the "
						 "transformation matrix because of incomplete OPI "
						 "comments. Image might be displaced or not displayed "
						 "at all.")
		
		else:
			# EPSF
			
			if 2.0 in self._version: ##self._hastransformationmatrix():
				self.msg("Using preset transformation matrix")
			elif self._ImagePosition:
				# If detected OPI version is 1.3 or gfxstate is empty, setup
				# transformation matrix
				w = self._getimage().size[0]
				h = self._getimage().size[1]
				llx = self._ImagePosition[0]
				lly = self._ImagePosition[1]
				ulx = self._ImagePosition[2]
				uly = self._ImagePosition[3]
				urx = self._ImagePosition[4]
				ury = self._ImagePosition[5]
				lrx = self._ImagePosition[6]
				lry = self._ImagePosition[7]
				a = Decimal(str((lrx - llx) / w))
				b = Decimal(str((lry - lly) / w))
				c = Decimal(str((ulx - llx) / h))
				d = Decimal(str((uly - lly) / h))
				tx = Decimal(str(llx))
				ty = Decimal(str(lly))
				# Reset any preset transformation matrix to device defaults
				self._gfxstate.append("initmatrix")
				self._gfxstate.append("[" + str(a) + " " + str(b) + " " +
									  str(c) + " " + str(d) + " " + str(tx) +
									  " " + str(ty) + "] concat")
				if self.verbose:
					self.msg("EPS Dimensions: " + str(self._getimage().size))
				if (self._ImageCropFixed and (self._ImageCropFixed[0] > 0 or
											  self._ImageCropFixed[1] > 0 or
											  w > self._ImageCropFixed[2] or
											  h > self._ImageCropFixed[3])):
					a = Decimal(str(w / (self._ImageCropFixed[2] -
										 self._ImageCropFixed[0])))
					d = Decimal(str(h / (self._ImageCropFixed[3] -
										 self._ImageCropFixed[1])))
					e = Decimal(str(- self._ImageCropFixed[0] * 
									(w / (self._ImageCropFixed[2] -
										  self._ImageCropFixed[0]))))
					f = Decimal(str(- (h - self._ImageCropFixed[3]) *
									(h / (self._ImageCropFixed[3] -
										  self._ImageCropFixed[1]))))
					self._gfxstate.append("[" + str(a) + " 0 0 " + str(d) +
										  " " + str(e) + " " + str(f) +
										  "] concat")
				# [w skewv skewh h movex movey]
			else:
				self.msg("WARNING: Could not determine or setup the "
						 "transformation matrix because of incomplete OPI "
						 "comments. Image might be displaced or not displayed "
						 "at all.")
			
		for line in self._gfxstate:
			self._raw_write(line + self.newline)

		if 2.0 in self.version:
			self._raw_write("%%BeginIncludedImage" + self.newline)
			if self._imageformat != "epsf":
				self._raw_write("%%IncludedImageDimensions: " +
								str(self._IncludedImageDimensions[0]) + " " +
								str(self._IncludedImageDimensions[1]) +
								self.newline)
			self._raw_write("%%IncludedImageQuality: " +
							str(self._IncludedImageQuality) + self.newline)
		
		self.msg("Inserting image data into postscript stream...")
		if self._imageformat != "epsf":
			if self._getimage().mode in ("1", "L"):
				if _mode == "b":
					self._raw_write("/rdstr{{[{currentfile}aload pop 2 index "
									"string{readstring pop}aload pop]cvx "
									"exch}repeat pop}B" + self.newline)
				else:
					self._raw_write("/rdstr{{[{currentfile}aload pop 2 index "
									"string{readhexstring pop}aload pop]cvx "
									"exch}repeat pop}B" + self.newline)
			
			if self._getimage().mode == "1":
				self._raw_write(str(self._getimage().size[0]) + " " +
								str(self._getimage().size[1]) + " " +
								str(bpp) + " [" +
								str(self._getimage().size[0]) + " 0 0 -" +
								str(self._getimage().size[1]) + " 0 " +
								str(self._getimage().size[1]) + "] " +
								str(int(math.ceil((self._getimage().size[0]) /
												  float(8)))) + " " +
								str(channels) + " rdstr" + self.newline)
				self._raw_write("[0 1] CreateImageDict" + self.newline)
				if self._ImageTransparency == False:
					# 'ImageDict image'
					bytes += 15
				else:
					# 'ImageDict imagemask'
					bytes += 19
			elif self._getimage().mode == "L":
				self._raw_write(str(self._getimage().size[0]) + " " +
								str(self._getimage().size[1]) + " " +
								str(bpp) + " [" +
								str(self._getimage().size[0]) + " 0 0 -" +
								str(self._getimage().size[1]) + " 0 " +
								str(self._getimage().size[1]) + "] " +
								str(self._getimage().size[0]) + " " +
								str(channels) + " rdstr" + self.newline)
				if self._hasdevicenprocset():
					if self._ImageInks or self._ImageColor:
						self._raw_write("[255 0] CreateImageDict" +
										self.newline)
					else:
						self._raw_write("[0 255] CreateImageDict" +
										self.newline)
					# 'ImageDict image'
					bytes += 15
				else:
					# 'image'
					bytes += 5 
			else:
				self._raw_write("/imagedata " + str(self._getimage().size[0] *
													channels) + " string def" +
								self.newline)
				self._raw_write(str(self._getimage().size[0]) + " " +
								str(self._getimage().size[1]) + " " +
								str(bpp) + self.newline)
				self._raw_write("[" + str(self._getimage().size[0]) +
								" 0 0 -" + str(self._getimage().size[1]) +
								" 0 " + str(self._getimage().size[1]) + "]" +
								self.newline)
				if _mode == "b":
					self._raw_write("{ currentfile imagedata readstring" +
									self.newline)
				else:
					self._raw_write("{ currentfile imagedata readhexstring" +
									self.newline)
				self._raw_write("	pop" + self.newline)
				self._raw_write("}" + self.newline)
				self._raw_write("false" + self.newline)
				self._raw_write(str(channels) + self.newline)
				# 'colorimage'
				bytes += 10
			bytes += len(self.newline) * 2

			# Insert the image
			if _mode == "b":
				self._raw_write("%%BeginData: " + str(bytes) + " Binary Bytes" +
								self.newline)
			else:
				self._raw_write("%%BeginData: " + str(bytes) + " Hex Bytes" +
								self.newline)
			if self._getimage().mode == "1":
				if self._ImageTransparency == False:
					self._raw_write("ImageDict image" + self.newline)
				else:
					self._raw_write("ImageDict imagemask" + self.newline)
			elif self._getimage().mode == "L":
				if self._hasdevicenprocset():
					self._raw_write("ImageDict image" + self.newline)
				else:
					self._raw_write("image" + self.newline)
			else:
				self._raw_write("colorimage" + self.newline)
			if _mode == "b":
				self._raw_write(imagedata)
			else:
				while imagedata:
					self._raw_write(imagedata[0:self._getimage().size[0]*2] +
									self.newline)
					imagedata = imagedata[self._getimage().size[0]*2:]
			
			self._raw_write(self.newline + "%%EndData" + self.newline)
		
		else:
			# EPSF
			if 2.0 in self._version and self._hastransformationmatrix():
				self._raw_write("tempmatrix setmatrix" + self.newline)
			self._raw_write("%%BeginDocument: " + self.escapefilename() +
							self.newline)
			self._raw_write(imagedata)
			self._raw_write(self.newline + "%%EndDocument" + self.newline)

		if 2.0 in self.version:
			self._raw_write("%%EndIncludedImage" + self.newline)
			self._raw_write("%%EndOPI" + self.newline)
		
		if 1.3 in self.version:
			self._raw_write("%%EndObject" + self.newline)

		self.msg("...OK")
		
		self._checkpurgecache(0)

		if self.verbose:
			self.info()
		
		self._reset()



class EPSImage:
	def __init__(self, filename):
		epsf = open(filename, "rb")
		data = epsf.read()
		epsf.close()
		if data[0:4] == "\xC5\xD0\xD3\xC6": # DOS EPS Binary File Header
			pscodebegin = int(binascii.hexlify(data[4:8][::-1]), 16)
			pscodelength = int(binascii.hexlify(data[8:12][::-1]), 16)
			self.data = data[pscodebegin:pscodebegin + pscodelength]
		elif data[0:2] == "%!": # ASCII EPS
			self.data = data
		else:
			self.data = ""
		self.format = "EPSF"
		self.info = {}
		self.mode = None
		self.palette = None
		if self.data:
			i = self.data.find("%%HiResBoundingBox")
			if i < 0:
				i = self.data.find("%%BoundingBox")
			if i >= 0:
				bbox = floatlist(self.data[i:i+128].split()[1:5])
				# %%BoundingBox, x2, y2, x2, y2
				self.info["boundingbox"] = bbox
				self.size = (bbox[2] - bbox[0], bbox[3] - bbox[1])
		else:
			self.size = (0, 0)
	def tostring(self):
		return self.data



def crc32(txt):
	bin = struct.pack('!l', zlib.crc32(txt))
	return binascii.hexlify(bin)

def joinpaths(paths):
	_path = paths[0]
	for segment in paths: _path = path.join(_path, segment)
	return _path

def floatlist(l):
	_l = []
	for v in l:
		try:
			_l.append(float(v))
		except:
			pass
	return _l

def intlist(l):
	_l = []
	for v in l:
		try:
			_l.append(int(round(float(v))))
		except:
			pass
	return _l

def strlist(l):
	_l = []
	for v in l:
		_l.append(str(v))
	return _l



if __name__=="__main__":

	opiparser = OPIparser()

	fi = None
	fo = None
	show_help = False

	for a in sys.argv[1:]:
		if a == "/?" or a == "-help" or a == "--help":
			show_help = True
			break
		a = a.split("=",1)
		if len(a):
			# ATTENTION: This means all checks below have to be done lowercase!
			a[0] = a[0].lower()
		if a[0] == "-preserveblack":
			opiparser._ImageCms_flags.append(ImageCms.FLAGS["PRESERVEBLACK"])
		elif a[0] == "-verbose":
			opiparser.verbose = True
		elif len(a) == 2:
			if a[0] == "-abortonfilenotfound":
				opiparser.abortonfilenotfound = bool(int(a[1]))
			elif a[0] == "-abortonerror":
				opiparser.abortonerror = bool(int(a[1]))
			elif a[0] == "-cachemegs":
				opiparser.cachemegs = float(a[1])
			elif a[0] == "-cmykgrayimages_stripcmy":
				opiparser.cmykgrayimages_stripcmy = bool(int(a[1]))
			elif a[0] == "-colorimagedownsamplethreshold":
				opiparser.ColorImageDownsampleThreshold = float(a[1])
			elif a[0] == "-colorimagedownsampletype":
				a[1] = a[1].lower()
				if a[1] == "nearest":
					opiparser.ColorImageDownsampleFilter = Image.NEAREST
				elif a[1] == "bilinear":
					opiparser.ColorImageDownsampleFilter = Image.BILINEAR
				elif a[1] == "bicubic":
					opiparser.ColorImageDownsampleFilter = Image.BICUBIC
				elif a[1] == "antialias":
					opiparser.ColorImageDownsampleFilter = Image.ANTIALIAS
			elif a[0] == "-colorimageminresolution":
				opiparser.ColorImageMinResolution = float(a[1])
			elif a[0] == "-colorimageresolution":
				opiparser.ColorImageResolution = float(a[1])
			elif a[0] == "-colorimageuseembeddedresolution":
				opiparser.ColorImageUseEmbeddedResolution = bool(int(a[1]))
			elif a[0] == "-convertcmyk": # legacy
				opiparser.convertcmykimages = bool(int(a[1]))
			elif a[0] == "-convertgrayimages":
				opiparser.convertgrayimages = bool(int(a[1]))
			elif a[0] == "-convertcmykimages":
				opiparser.convertcmykimages = bool(int(a[1]))
			elif a[0] == "-convertk": # legacy
				opiparser.convertgrayimages = bool(int(a[1]))
			elif a[0] == "-detectcmykgrayimages":
				opiparser.detectcmykgrayimages = bool(int(a[1]))
			elif a[0] == "-downsamplecolorimages":
				opiparser.DownsampleColorImages = bool(int(a[1]))
			elif a[0] == "-downsamplegrayimages":
				opiparser.DownsampleGrayImages = bool(int(a[1]))
			elif a[0] == "-downsamplemonoimages":
				opiparser.DownsampleMonoImages = bool(int(a[1]))
			elif a[0] == "-grayimagedownsamplethreshold":
				opiparser.GrayImageDownsampleThreshold = float(a[1])
			elif a[0] == "-grayimagedownsampletype":
				a[1] = a[1].lower()
				if a[1] == "nearest":
					opiparser.GrayImageDownsampleFilter = Image.NEAREST
				elif a[1] == "bilinear":
					opiparser.GrayImageDownsampleFilter = Image.BILINEAR
				elif a[1] == "bicubic":
					opiparser.GrayImageDownsampleFilter = Image.BICUBIC
				elif a[1] == "antialias":
					opiparser.GrayImageDownsampleFilter = Image.ANTIALIAS
			elif a[0] == "-grayimageminresolution":
				opiparser.GrayImageMinResolution = float(a[1])
			elif a[0] == "-grayimageresolution":
				opiparser.GrayImageResolution = float(a[1])
			elif a[0] == "-grayimageuseembeddedresolution":
				opiparser.GrayImageUseEmbeddedResolution = bool(int(a[1]))
			elif a[0] == "-hires":
				if sys.platform == 'win32':
					opiparser.hirespath = unicode(a[1], "cp437", "replace")
				else:
					opiparser.hirespath = unicode(a[1], "utf-8", "replace")
			elif a[0] == "-in":
				if sys.platform == 'win32':
					fi = unicode(a[1], "cp437", "replace")
				else:
					fi = unicode(a[1], "utf-8", "replace")
			elif a[0] == "-imagecropthreshold":
				opiparser.imagecropthreshold = float(a[1])
			elif a[0] == "-intent":
				opiparser.intent = a[1].lower()
			elif a[0] == "-log":
				if sys.platform == 'win32':
					opiparser.log = unicode(a[1], "cp437", "replace")
				else:
					opiparser.log = unicode(a[1], "utf-8", "replace")
			elif a[0] == "-lores":
				if sys.platform == 'win32':
					opiparser.lorespath = unicode(a[1], "cp437", "replace")
				else:
					opiparser.lorespath = unicode(a[1], "utf-8", "replace")
			elif a[0] == "-mode":
				opiparser.mode = a[1].lower()
			elif a[0] == "-monoimagedownsamplethreshold":
				opiparser.MonoImageDownsampleThreshold = float(a[1])
			elif a[0] == "-monoimagedownsampletype":
				a[1] = a[1].lower()
				if a[1] == "nearest":
					opiparser.MonoImageDownsampleFilter = Image.NEAREST
				elif a[1] == "bilinear":
					opiparser.MonoImageDownsampleFilter = Image.BILINEAR
				elif a[1] == "bicubic":
					opiparser.MonoImageDownsampleFilter = Image.BICUBIC
				elif a[1] == "antialias":
					opiparser.MonoImageDownsampleFilter = Image.ANTIALIAS
			elif a[0] == "-monoimageminresolution":
				opiparser.MonoImageMinResolution = float(a[1])
			elif a[0] == "-monoimageresolution":
				opiparser.MonoImageResolution = float(a[1])
			elif a[0] == "-monoimageuseembeddedresolution":
				opiparser.MonoImageUseEmbeddedResolution = bool(int(a[1]))
			elif a[0] == "-newline":
				if a[1] == "\\r":
					opiparser.newline = "\r"
				elif a[1] == "\\r\\n":
					opiparser.newline = "\r\n"
			elif a[0] == "-out":
				if sys.platform == 'win32':
					fo = unicode(a[1], "cp437", "replace")
				else:
					fo = unicode(a[1], "utf-8", "replace")
			elif a[0] == "-outgrayprofile":
				opiparser.ICCProfiles["out_gray"].fileName = a[1]
			elif a[0] == "-outmonoprofile": # legacy
				opiparser.ICCProfiles["out_RGB_gray"].fileName = a[1]
			elif a[0] == "-outrgbgrayprofile":
				opiparser.ICCProfiles["out_RGB_gray"].fileName = a[1]
			elif a[0] == "-outprofile":
				opiparser.ICCProfiles["out"].fileName = a[1]
			elif a[0] == "-proofgrayprofile":
				opiparser.ICCProfiles["proof_gray"].fileName = a[1]
			elif a[0] == "-proofintent":
				opiparser.proofintent = a[1].lower()
			elif a[0] == "-proofrgbgrayprofile":
				opiparser.ICCProfiles["proof_RGB_gray"].fileName = a[1]
			elif a[0] == "-proofprofile":
				opiparser.ICCProfiles["proof"].fileName = a[1]
			elif a[0] == "-sameprofiles":
				opiparser.sameprofiles_sets.append([desc_or_md5.strip('"')
													for desc_or_md5 in
													a[1].split(",")])
			elif a[0] == "-usecache":
				opiparser.usecache = bool(int(a[1]))
			elif a[0] == "-usediskcache":
				opiparser.usediskcache = bool(int(a[1]))
			elif a[0] == "-workingcmykprofile":
				opiparser.ICCProfiles["working_CMYK"].fileName = a[1]
			elif a[0] == "-workinggrayprofile":
				opiparser.ICCProfiles["working_gray"].fileName = a[1]
			elif a[0] == "-workingrgbprofile":
				opiparser.ICCProfiles["working_RGB"].fileName = a[1]

	if (not show_help and fi and fo and opiparser.hirespath and
		opiparser.lorespath):
		opiparser.parse(fi, fo)
	else:
		print "pyOPI build", opiparser.build
		print ""
		print "USAGE: %s <options>" % sys.argv[0]
		print ""
		print "REQUIRED OPTIONS:"
		print " -hires=\"<path to hires images>\""
		print " -in=[stdin|<path to postscript input file>]"
		print "   read from stdin or postscript input file"
		print " -lores=\"<path to lores images>\""
		print " -out=[stdout|<path to postscript output file>]"
		print "   write to stdout or postscript output file"
		print ""
		print "ADDITIONAL OPTIONS:"
		print " -abortonerror=[0|1]"
		print "   0 = do not abort on error"
		print "   1 = abort on error (default)"
		print " -abortonfilenotfound=[0|1]"
		print "   0 = do not abort if image file not found"
		print "   1 = abort if image file not found (default)"
		print " -cachemegs=256"
		print "   max RAM cache size for images in megabytes"
		print " -cmykgrayimages_stripcmy=[0|1] (use along with -detectcmykgrayimages)"
		print "   0 = do not strip CMY from K-only images (default) when not converting"
		print "   1 = strip CMY from K-only images when not converting"
		print " -colorimagedownsamplethreshold=2.0"
		print " -colorimagedownsampletype=[nearest|bilinear|bicubic|antialias (default)]"
		print " -colorimageresolution=300.0"
		print "   color image downsampling target resolution if"
		print "   actual resolution > (colorimageresolution * colorimagedownsamplethreshold)"
		print " -colorimageuseembeddedresolution=[0|1]"
		print "   0 = use colorimageresolution"
		print "   1 = use actual resolution if set (default)"
		print " -convertgrayimages=[0|1]"
		print "   0 = do not convert gray images (default)"
		print "   1 = convert gray images"
		print " -convertcmykimages=[0|1] (use along with -outprofile)"
		print "   0 = do not convert CMYK images"
		print "   1 = convert CMYK images (default)"
		print " -detectcmykgrayimages=[0|1] (use along with -convertcmykimages)"
		print "   0 = do not detect CMYK gray (CMY empty, only K contains data) images"
		print "   1 = detect CMYK gray (CMY empty, only K contains data) images (default)"
		print " -downsamplecolorimages=[0|1] (use along with -colorimageresolution)"
		print "   0 = do not downsample color images"
		print "   1 = downsample color images (default)"
		print " -downsamplegrayimages=[0|1] (use along with -grayimageresolution)"
		print "   0 = do not downsample gray images"
		print "   1 = downsample gray images (default)"
		print " -downsamplemonoimages=[0|1] (use along with -monoimageresolution)"
		print "   0 = do not downsample 1-Bit images (default)"
		print "   1 = downsample 1-Bit images"
		print " -grayimagedownsamplethreshold=2.0"
		print " -grayimagedownsampletype=[nearest|bilinear|bicubic|antialias (default)]"
		print " -grayimageresolution=300.0"
		print "   grayscale image downsampling target resolution if"
		print "   actual resolution > (grayimageresolution * grayimagedownsamplethreshold)"
		print " -grayimageuseembeddedresolution=[0|1]"
		print "   0 = use grayimageresolution"
		print "   1 = use actual resolution if set (default)"
		print " -imagecropthreshold=1.1"
		print "   treshold above which actual image data is discarded when cropped."
		print " -intent=[a|b|p|r|s] (a = absolute, b = relative with black point compensation"
		print "   p = perceptive [default], r = relative, s = saturation)"
		print "   intent for image conversion to output colorspace"
		print " -log=\"<path to logfile>\""
		print " -mode=[a|b]"
		print "   output mode for inserted image data"
		print "   a = ASCII"
		print "   b = binary (default)"
		print " -monoimagedownsamplethreshold=2.0"
		print " -monoimagedownsampletype=[nearest (default)|bilinear|bicubic|antialias]"
		print " -monoimageresolution=1200.0"
		print "   1-Bit image downsampling target resolution if"
		print "   actual resolution > (monoimageresolution * monoimagedownsamplethreshold)"
		print " -monoimageuseembeddedresolution=[0|1]"
		print "   0 = use monoimageresolution"
		print "   1 = use actual resolution if set (default)"
		print " -newline=[\\n|\\r|\\r\\n]"
		print "   newline character to use for inserted OPI comments"
		print " -outgrayprofile=\"profile.icc\""
		print "   icc profile for converting grayscale images to output colorspace"
		print " -outRGBgrayprofile=\"profile.icc\""
		print "   icc profile for converting 'R=G=B' images to output colorspace"
		print " -outprofile=\"profile.icc\""
		print "   icc profile for converting color images to output colorspace"
		print " -preserveblack"
		print "   preserve black channel as much as possible when converting CMYK to CMYK"
		print " -proofintent=[a|b|p|r|s] (a = absolute, b = relative with black point"
		print "  compensation, p = perceptive [default], r = relative, s = saturation)"
		print "   intent for conversion to proofing colorspace"
		print " -proofgrayprofile=\"profile.icc\""
		print "   icc profile for converting grayscale images to proofing colorspace"
		print " -proofRGBgrayprofile=\"profile.icc\""
		print "   icc profile for converting 'R=G=B' images to proofing colorspace"
		print " -proofprofile=\"profile.icc\""
		print "   icc profile for converting color images to proofing colorspace"
		print " -sameprofiles=\"Profile Description\"[,\"Profile Description\"[,...]]"
		print "   ICC Profiles which match the description(s) will be treated as identical"
		print "   (e.g. no color conversion will occur between them)"
		print " -sameprofiles=MD5[,MD5[,...]]"
		print "   ICC Profiles which match the MD5 checksum(s) will be treated as identical"
		print "   (e.g. no color conversion will occur between them)"
		print " -usecache=[0|1]"
		print "   0 = do not use RAM cache for images"
		print "   1 = use RAM cache for images"
		print " -verbose"
		print "   verbose logging"
		print " -workingCMYKProfile=\"profile.icc\""
		print "   profile to use for color converting CMYK images without embedded profile"
		print " -workingGrayProfile=\"profile.icc\""
		print "   profile to use for color converting gray images without embedded profile"
		print " -workingRGBProfile=\"profile.icc\""
		print "   profile to use for color converting RGB images without embedded profile"
