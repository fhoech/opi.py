# -*- coding: utf-8 -*-

from thread import start_new_thread
from time import sleep, strftime
import subprocess as sp
import time
import wx

class LogWindow(wx.Frame):

	def __init__(self, title = "Log", size = (600, 600), format = "%Y-%m-%d %H:%M:%S "):
		## frame and textbox
		wx.Frame.__init__(self, None, -1, "", style = wx.DEFAULT_FRAME_STYLE)
		self.log = wx.TextCtrl(self, -1, "", style = wx.TE_MULTILINE | wx.TE_READONLY)

		## layout
		self.SetTitle(title)
		self.SetSize(size)

		## format for strftime
		self.format = format

	def write(self, line = None):
		if line:
			self.log.AppendText(strftime(self.format) + line + "\n")
		else:
			self.log.AppendText("\n")


if __name__=="__main__":
	app = wx.PySimpleApp()
	logWindow = LogWindow("Log window", (600, 600))
	def main():
		logWindow.write("Log window example")
		logWindow.write()
		
		tstart = time.time()
		count = 10
		for i in range(0, count):
			logWindow.write("Closing in " + str(count - i) + " seconds...")
			time.sleep(1)
		
		print time.time() - tstart
		
		app.ExitMainLoop()
	start_new_thread(main, ())
	logWindow.Show()
	app.MainLoop()