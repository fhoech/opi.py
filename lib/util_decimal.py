# -*- coding: utf-8 -*-

import decimal
import math


def float2dec(f, digits=10):
	parts = str(f).split(".")
	if len(parts) > 1:
		if parts[1][:digits] == "9" * digits:
			f = math.ceil(f)
		elif parts[1][:digits] == "0" * digits:
			f = math.floor(f)
	return decimal.Decimal(str(f))


def stripzeros(n):
	"""
	Strip zeros and convert to decimal.
	
	Will always return the shortest decimal representation
	(1.0 becomes 1, 1.234567890 becomes 1.23456789).
	
	"""
	n = str(n)
	if n.find(".") < 0:
		n += "."
	try:
		n = decimal.Decimal(n.rstrip("0"))
	except decimal.InvalidOperation, exception:
		pass
	return n
