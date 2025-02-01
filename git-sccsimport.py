#!/usr/bin/env python3
#
# git-sccsimport -- Import deltas collectively from SCCS files into git
#
#ident	"%Z%%Y%:%M%	%I%	%E% %U% (%Q%)"
#
# Author: James Youngman <jay@gnu.org>
# Copyright: 2008 James Youngman <jay@gnu.org>
# License: GNU GPL version 2 or later <http://www.gnu.org/licenses/old-licenses/gpl-2.0.html>
#
# Additional Author: Greg A. Woods <woods@robohack.ca>
# Copyright: 2025 Greg A. Woods <woods@robohack.ca>
# License: GNU GPL version 2 or later <http://www.gnu.org/licenses/old-licenses/gpl-2.0.html>
#
# Import this from SCCS to Git with:
#
#	if [ ! -d /work/woods/g-git-sccsimport/.git ]; then
#		mkdir -p /work/woods/g-git-sccsimport
#		cd /work/woods/g-git-sccsimport
#		git init
#		hub create robohack/git-sccsimport
#	fi
#	cd ~/src
#	git-sccsimport --tz=-0800 --stdout --maildomain=robohack.ca SCCS/s.git-sccsimport.py | gsed '0,/^committer [^0-9]* \([0-9]*\) -0800/s//committer Jay Youngman <jay@gnu.org> 1200826930 +0100/' | (cd /work/woods/g-git-sccsimport && git fast-import && git checkout master -- . )
#	cd /work/woods/g-git-sccsimport
#	git push -u origin master
#
#
# ToDo:
#
# - add controls and defaults for timezones
#
# - fix the calling conventions (command-line API) to be more like:
#
#	mkdir my-project-converted-to-git
#       cd my-project-converted-to-git
#       git init
#       git-sccsimport $PROJECTDIR [...]
#
# - support branches? (CSRG did not really use branches [only a few somewhat
#   scattered files in all of 4.4BSD-Alpha have branch numbers, and only a very
#   few have branch numbers other than "R.L.1.S" (i.e. ".1"), mostly on a few
#   release and version identifying files in Sendmail.
#
#   - currently branch deltas just appear in chronological order in the git
#     commit stream.
#
#   - perhaps we could just commit branch deltas to "br-<filename>-R.L.B" refs
#     (which are created with a "reset" section)?
#
# - fuzzy commit comparison would work better if delta sorting was smarter,
#   e.g. if it could do some kind of "sliding window sort" on the comment text
#   over a group of commits.
#
# - can the SCCS "descriptive text" (:FD:) be used and useful in Git? (store it
#   in a special attribute?)
#
# - what to do with the text from any 'm', 'q', and 't' flags?
#
# - consider incremental import support
#
#   - it already essentially works by brute force (full re-import), but it could
#     be optimized, and with new calling conventions it might work like:
#
#	cd my-project-converted-to-git
#	git-sccsimport --incr $PROJECTDIR [...]
#
#   - might keep a rev list ala git-cvsimport (or just last rev?)
#
#     - or does the last rev's timestamp suffice?
#
#   - how does this interact with branches or does it matter?
#
#   - this might help in situations where something happens to cause a diverging
#     path, e.g. a tag is applied in a different place.
#
# - there probably should be a --quiet option to suppress progress info
#
"""A fast git importer for SCCS files.

It will import deltas collectively from groups of SCCS files into a fresh git
repository using "git fast-import".

How to use this program:

Let's assume you have some SCCS files in $PROJECTDIR and want to convert them to
a git repository in the directory $NEWGIT.

First, make sure the SCCS (or CSSC) binaries are on your $PATH.  Then do this:

  cd "$PROJECTDIR"
  git-sccsimport --init --git-dir="$NEWGIT" --dirs .

Notice that git-sccsimport is being run with its working directory as the root
of the tree of SCCS files.  This is because the relative path from your working
directory to the SCCS file is also used as the (path)name of the file in the
resulting git repository.

Since git-sccsimport always does a complete import, and because by default it
tries to merge commits with the same message text and author, it can create a
diverging tip if something weird happens between successive imports to the same
Git repository (e.g. a new matching commit is made, or new tag is implied).

When this happens git-fast-import will warn with a message like the following:

  warning: Not updating refs/heads/master (new tip 6e7cd4a1aea270d27f588e3bed356a657bedd358 does not contain 82b901b23b94919807aef4ac65792ca2bd2f9512)

In this case if you must press on then you can reset your branch to the new tip
of the import with "git reset --hard <new-tip>".  Note though that this will
cause other clones to see history being rewritten, but here this is intended and
any other clones just have to deal with it.

This program has been used to convert the 12,613 valid SCCS files in the UCB
CSRG BSD archives, reading 105,024 deltas, creating 53,991 Git commits.  The
python-3.9 process ran at about 150MB resident (205MB total), and with the "new"
fast (direct header parsing) method it completed in just under 18 minutes (on an
8 vCPU, 22GB, Xen VM on Dell PE2950 with Intel Xeon E5440 CPUs @ 2.83GHz).

"""
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo
import errno
import optparse
import os
import os.path
import pwd
import re
import resource
import stat
import string
import subprocess
import sys

from operator import attrgetter

SCCS_ESCAPE = ord(b'\x01')	# <CTRL-A>

# this will normally not be used -- see the AuthorMap option....
#
MAIL_DOMAIN = None

DEFAULT_USER_TZ = None	# Default to local time zone

IMPORT_REF = None


# Two checkins separated by more than FUZZY_WINDOW will never be considered part
# of the same commit; N.B. even if they have the same non-empty comment,
# commiter, and MRs.  (I.e. this can be a relatively large number, e.g. 1 day,
# or even potentially a much longer time, such as a week.)
FUZZY_WINDOW = 24.0 * 60.0 * 60.0 * 7.0


debug = False
verbose = False

DoTags = True

class ImportFailure(Exception):
	pass

class CommandFailure(Exception):
	pass

class UsageError(Exception):
	pass

class AbstractClassError(Exception):
	pass


def Usage(who, retval, f, e):
	if e:
		print(e, file=f)
		print(("usage: %s sccs-file [sccs-file...]" % (who,)), file=f)

	if retval:
		sys.exit(retval)

	return retval


def NotImporting(file, sid, reason):
	if sid:
		msg = ("%s: not importing SID %s: %s"
		       % (file, sid, reason))
	else:
		msg = ("%s: not importing this file: %s"
		       % (file, reason))

	print(msg, file=sys.stderr)


def ReportCommandFailure(command, returncode, errors):
	if not errors:
		errors = ""

	if returncode < 0:
		msg = ("%s: killed by signal %s" % (command, -(returncode),))
	else:
		msg = ("%s: returned exit status %d" % (command, returncode,))

	raise CommandFailure("%s\n%s" % (errors, msg,))


def RunCommand(commandline, text=True):
	try:
		if debug:
			msg = ("Running command: %s\n"
			       % (" ".join(commandline),))
			sys.stderr.write(msg)

		child = subprocess.Popen(commandline,
					 text=text,
					 close_fds = True,
					 stdin =subprocess.PIPE,
					 stdout=subprocess.PIPE,
					 stderr=subprocess.PIPE)
		output, errors = child.communicate(None)
		# Some stderr output is normal (warnings, etc.)
		if child.returncode != 0:
			ReportCommandFailure(commandline[0], child.returncode, errors)
		else:
			if errors and debug:
				print(("%s stderr: %s" % (commandline[0], errors,)), file=sys.stderr)
			return output
	except OSError as oe:
		msg = ("Failed to run '%s': %s (%s)"
		       % (commandline[0], oe,
			  errno.errorcode[oe.errno]))
		if debug:
			sys.stderr.write(msg + "\n")
		raise OSError(msg)
	# for now we'll also just convert CommandFailure to ImportFailure
	except CommandFailure as cmd_failure:
		if verbose:
			print((cmd_failure), file=sys.stderr)
		raise ImportFailure(cmd_failure)


def RunPrs(options):
	commandline = PRS.split(" ")
	commandline.extend(options)
	return RunCommand(commandline)

def RunVal(options):
	commandline = VAL.split(" ")
	commandline.extend(options)
	return RunCommand(commandline)

def IsValidSccsFile(filename):
	try:
		output = RunVal([filename])
		#print(("%s: %s" % (VAL, output,)), file=sys.stderr)
		return True
	except ImportFailure:
		return False
	except OSError as oe:
		print(("\nVAL failed: %s" % (oe,)), file=sys.stderr)
		sys.exit(1)

def GetBody(sfile, seqno, expand_keywords):
	commandline = GET.split(" ")
	options = ["-p", "-s", ("-a%d" % (seqno,))]
	if not expand_keywords:
		options.append("-k")

	options.append(sfile)
	commandline.extend(options)
	return RunCommand(commandline, text=False)


def FileMode(filename):
	return stat.S_IMODE(os.stat(filename).st_mode)


def HeaderLines(filename):
	"""Extract all the header lines from an SCCS file, as per sccsfile(5)."""
	header_end = b"^%cT" % (SCCS_ESCAPE,)
	result = []
	try:
		f = open(filename, "rb")
		for line in f.readlines():
			if line[0] == SCCS_ESCAPE and line[1] == ord(b'T'): # and line[2] == '\n'
				result.append(line)
				break
			else:
				result.append(line)
		return result

	finally:
		f.close()


class SccsFileQuerySlow():
	"""Extract information from SCCS files by running prs(1).

	This is now only used for testing -- it is significantly slower than
	SccsFileQueryFast() as it requires running a separate PRS command for
	every SID.

	(SccsFileQueryBase is ignored.)

	"""
	@staticmethod
	def FetchDeltaProperties(sid, sccsfile):
		fmt = (":Dy:/:Dm:/:Dd:%(esc)c" # 0 delta creation date
		       ":Th:::Tm:::Ts:%(esc)c" # 1 delta creation time (24h)
		       ":C:%(esc)c"            # 2 checkin comments
		       ":DS:%(esc)c"           # 3 seqno
		       ":DP:%(esc)c"           # 4 parent seqno
		       ":DT:%(esc)c"           # 5 delta type (R or D)
		       ":I:%(esc)c"            # 6 SID
		       ":MR:%(esc)c"           # 7 MR numbers
		       ":P:"                   # 8 Perpetrator (committer)
		       % { 'esc': chr(1) })    # <CTRL-A> as separator
		cmdline = [("-d%s" % (fmt,)), ("-r%s" % (sid,)), sccsfile.filename]
		propdata = SccsFileQuerySlow.RunPrs(cmdline).rstrip('\n')
		#print(("PRSout: ", propdata),  file=sys.stderr)
		#print(("props: %s" % (propdata.split(chr(1)),)), file=sys.stderr)
		return propdata.split(chr(1))

	@staticmethod
	def GetRevisionList(filename, headerlines):
		revisions = SccsFileQuerySlow.RunPrs(["-d:I: ", "-e", filename])
		return revisions.split()

	# "Arbitrary text surrounded by the bracketing lines @t and @T.  This
	# comments section typically will contain a description of the file's
	# purpose."
	#
	# (xxx not yet used)
	#
	@staticmethod
	def GetFileDesc(filename, headerlines):
		desc = SccsFileQuerySlow.RunPrs(["-d:FD: ", filename])

		if desc == "none": # xxx need to trim to ignore newlines?
			return ""
		else:
			return desc


class SccsFileQueryFast():
	"""Extract information from SCCS files.

	(Parses SCCS files directly, as per sccsfile(5).)

	"""
	sid_key = b'%cd D ' % (SCCS_ESCAPE,) # ignore removed (R) deltas

	@staticmethod
	def GetRevisionList(filename, headerlines):
		result = []
		for line in headerlines:
			if line.startswith(SccsFileQueryFast.sid_key):
				fields = line.split()
				result.append(fields[2].decode())

		return result

	# "Arbitrary text surrounded by the bracketing lines @t and @T.  This
	# comments section typically will contain a description of the file's
	# purpose."  PRS uses ":FD:" as the keyword to print this.
	#
	# (xxx not yet used)
	#
	@staticmethod
	def GetFileDesc(filename, headerlines):
		result = []
		for line in headerlines:
			if line[1] == 't':
				started = True
				continue
			if line[1] == 'T':
				break
			if started:
				result.append(line)

		return result

	@staticmethod
	def FetchDeltaProperties(sid, sccsfile):
		found = False
		props = []
		comments = []
		MRs = []
		comment_key = b'%cc ' % (SCCS_ESCAPE,)
		MR_key = b'%cm ' % (SCCS_ESCAPE,)
		delta_end_key = b'%ce' % (SCCS_ESCAPE,)

		for line in sccsfile.headerlines:
			if not found and line.startswith(SccsFileQueryFast.sid_key):
				#
				# xxx note we're decoding lines from bytes to
				# strings as UTF-8, but maybe we should use a
				# different input encoding?
				#
				line = line.decode().rstrip('\n')
				#print(("line: ", line), file=sys.stderr)
				fields = line.split()
				#print(("fields: %s" % (fields,)), file=sys.stderr)
				if fields[2] == sid:
					found = True
					props = [ fields[3], # 0 creation date
						  fields[4], # 1 creation time
						  None,      # 2 checkin comment (see else:)
						  fields[6], # 3 seqno
						  fields[7], # 4 parent seqno
						  fields[1], # 5 delta type (R or D, but always D)
						  fields[2], # 6 SID
						  None,      # 7 MR list (see else:)
						  fields[5], # 8 Perpetrator (committer)
					]
					continue
			if found:
				if line.startswith(comment_key):
					#print(("comment: %s" % (line,)), file=sys.stderr)
					comments.append(line[3:].decode())
				elif line.startswith(MR_key):
					#print(("MR: %s" % (line,)), file=sys.stderr)
					MRs.append(line[3:].decode())
				elif line.startswith(delta_end_key):
					break

		if found:
			#print(("comments: %s" % (comments,)), file=sys.stderr)
			props[2] = "".join(comments)
			#print(("MRs: ", MRs), file=sys.stderr)
			#
			# MRs are collected as a newline-separated list of numbers
			# because that's what PRS gives us in the slow version.
			#
			props[7] = "".join(MRs)

			#print(("props: %s" % (props,)), file=sys.stderr)
			return props
		else:
			# xxx should probably be an assert -- we found it once already!
			#print(("%s: sid: %s: NOT FOUND" % (sccsfile.filename,sid,)), file=sys.stderr)
			return None


def SccsFileQuery():
	"""Factory method for objects that query SccsFileQuery objects -- Slow or Fast"""
	return SccsFileQueryFast()


class Delta(object):
	"""Represents the properties of an SCCS delta that we
	import into git."""
	def __init__(self, sccsfile, sid, qif, *args, **kwargs):
		super(Delta, self).__init__(*args, **kwargs)
		self._sccsfile = sccsfile
		self._sid = sid
		self._qif = qif
		self.FetchDeltaProperties()

	def __repr__(self):
		return 'Delta(%s, "%s")' % (repr(self._sccsfile), self._sid)

	def FetchDeltaProperties(self):
		"""Query the properties of this delta from the SCCS file."""
		props = self._qif.FetchDeltaProperties(self._sid,
						       self._sccsfile)
		assert len(props)>1, "%s %s %s" % (self._sccsfile._filename, self._sid, props,)
		(self._comment, self._seqno, self._parent_seqno, self._type,
		 sidcheck, mrlist, self._committer) = props[2:]
		self._ui = GetUserInfo(self._committer, MAIL_DOMAIN, DEFAULT_USER_TZ)
		self.SetTimestamp(props[0], props[1])
		#print(("DeltaProperties: %s" % (self)), file=sys.stderr)
		self._seqno = int(self._seqno)
		self._parent_seqno = int(self._parent_seqno)
		if self._comment == "\n":
			self._comment = None

		assert sidcheck==self._sid
		self._mrs = mrlist.split()

	def SameFuzzyCommit(self, other):
		#print(("SameFuzzyCommit: comparing\n1: %s with\n2: %s"
		#		     % (self, other)), file=sys.stderr)
		if self._comment != other._comment:
			return False
		elif self._committer != other._committer:
			return False
		elif self._mrs != other._mrs:
			return False
		else:
			delta = abs(other._timestamp - self._timestamp)
			if delta > FUZZY_WINDOW or self._comment == "":
				return False
			else:
				return True

	def SetTimestamp(self, checkin_date, checkin_time):
		try:
			year, month, monthday = [int(f) for f in checkin_date.split("/")]
		except ValueError:
			raise ImportFailure("Unexpected date format: %s"
					    % (checkin_date,))
		try:
			h,m,s = [int(f) for f in checkin_time.split(":")]
		except ValueError:
			raise ImportFailure("Unexpected time format: %s"
					    % (checkin_time,))
		microsec = 0

		if year < 100:
			# Apply the y2k rule (see the "Year 2000 Issues" section
			# of the CSSC documentation).
			if year < 69:
				year += 2000
			else:
				year += 1900

		# The timezone currently defaults to the host's timezone
		# (i.e. assuming the import is being done on a machine in the
		# same timezone as the original SCCS source server lived),
		# but this can be overridden with the --tz option.
		#
		# With the addition of the AuthorMap file we can also adjust
		# timestamps on a per-author basis.
		#
		tz = self._ui.tz or DEFAULT_USER_TZ

		if tz:
			# Treat the specified time as in the user-mapped zone or the
			# zone specified via --tz.
			cdate = datetime(year, month, monthday,
						  h, m, s,
						  microsec, tzinfo=tz)
		else:
			# Since the naive datetime is presumed local, and astimezone()
			# would convert to local, the result is that the specified time
			# is for the local system zone.
			cdate = datetime(year, month, monthday,
						  h, m, s,
						  microsec, None).astimezone()

		# Currently we can handle one "move", where the timezone changes at
		# some point, through the --move-date and --move-zone options. A future
		# version might allow a list of such moves, maybe read from a file or
		# using repeated command-line options.
		#
		# Note that user-mapped timezones take precedence over MoveDate/MoveZone.
		#
		if self._ui.tz is None and MoveDate is not None and cdate >= MoveDate:
			cdate = datetime(year, month, monthday,
						  h, m, s,
						  microsec, tzinfo=MoveZone)

		# git fast-import requires the timestamp to be measured in
		# seconds since the Unix epoch.
		#
		self._timestamp = cdate.timestamp()
		self._tz_offset = cdate.strftime("%z")

	def GitTimestamp(self):
		# We also pass timezone information from the AuthorMap (or local
		# timezone) by setting the appropriate <offutc> value here.
		# N.B. the timestamp must still be in UTC -- <offutc> is only
		# used to advise formatting of timestamps in log reports and
		# such.
		return "%d %s" % (self._timestamp, self._tz_offset,)

	def GitComment(self):
		"""Format a comment, noting any MRs as 'Issue' numbers"""
		comment = "" # commit comment is mandatory

		if self._comment:
			comment = self._comment

		if self._mrs:
			comment += "\n"
			comment += "Issue"
			if len(self._mrs) > 1:
				comment += "s"
			comment += ": "
			comment += ", ".join(map(lambda mr: '#' + mr, self._mrs))

		return comment

	def SidLevel(self):
		return int(self._sid.split(".")[0])
	def SidRev(self):
		return int(self._sid.split(".")[1])

class SccsFile(object):
	def __init__(self, name, *args, **kwargs):
		super(SccsFile, self).__init__(*args, **kwargs)
		self._filename = name
		self._headerlines = HeaderLines(name)
		qif = SccsFileQuery()
		revisions = filter(self.GoodRevision, qif.GetRevisionList(name, self._headerlines))
		self._deltas = [Delta(self, sid, qif) for sid in revisions]
		self._gitname = self.GitFriendlyName(self._GottenName())
		if FileMode(self._filename) & 0o111:
			self._gitmode = "755"
		else:
			self._gitmode = "644"

	gitname = property(lambda self: self._gitname)
	gitmode = property(lambda self: self._gitmode)
	filename = property(lambda self: self._filename)
	headerlines = property(lambda self: self._headerlines)
	deltas = property(lambda self: self._deltas)

	def __repr__(self):
		return "SccsFile(r'%s')" % (self._filename,)

	@staticmethod
	def GitFriendlyName(name):
		"""Clean up filenames.

		git-fastimport does not like leading or trailing slashes, or
		. or .. in file names. This method removes such things.

		"""
		if os.path.isabs(name):
			raise ImportFailure("%s is an absolute path name" % (name,))
		drive, path = os.path.splitdrive(name)
		return os.path.normpath(path)

	def _GottenName(self):
		"""Map SCCS filename to Makefile name.

		Convert the name of an SCCS file to the name of the working file
		as would be assumed by make.

		Specifically, the s. prefix is stripped, and if the s.file is in
		a directory called SCCS, that directory is stripped out of the
		path also.

		"""
		head, tail = os.path.split(self._filename)
		if tail.startswith("s."):
			tail = tail[2:]

		dirhead, dirtail = os.path.split(head)
		if dirtail == "SCCS":
			head = dirhead

		return os.path.join(head, tail)

	def GoodRevision(self, sid):
		comps = sid.split(".")
		if len(comps) > 1 and all(int(x) > 0 for x in comps):
			return True
		else:
			NotImporting(self._filename, sid,
				     "Invalid SID")
			return False


class GitImporter(object):
	"""Handles communications with git-fast-import."""

	def __init__(self, *args, **kwargs):
		super(GitImporter, self).__init__(*args, **kwargs)
		self._next_mark = 1
		self._command = None
		self._importer = None
		self._write_to_stdout = False
		self._used_tags = {}

	def StartImporter(self):
		args = ["git","fast-import"]
		self._command = " ".join(args)
		self._importer = subprocess.Popen(args,
						  close_fds=True,
						  stdin=subprocess.PIPE)

	def SendToStdout(self):
		self._command = None
		self._importer = None
		self._write_to_stdout = True

	def GetNextMark(self):
		"""Get the next unused idnum for a mark statement."""
		result = self._next_mark
		self._next_mark += 1
		return result

	def Write(self, s, enc=True):
		"""Write some data to the importer."""
		if self._write_to_stdout:
			# xxx stdout is open in text mode (?)
			sys.stdout.buffer.write(s.encode() if enc else s)
		else:
			assert self._importer
			self._importer.stdin.write(s.encode() if enc else s)

	def WriteData(self, data, enc=True):
		"""Emit a data command followd by a blob of data."""
		self.Write("data %d\n" % (len(data),))
		self.Write(data, enc=enc)
		self.Write("\n")

	def Done(self):
		if self._importer:
			self._importer.stdin.close()
			returncode = self._importer.wait()
			if returncode != 0:
				ReportCommandFailure(self._command, returncode, None)
			else:
				print(("%s completed successfully"
						     % (self._command,)), file=sys.stderr)

				output = RunCommand(["git",
						     "--git-dir=%s" % (GitDir,),
						     "--work-tree=%s" % (os.path.dirname(GitDir),),
						     "gc", "--aggressive"]) # n.b. no --progress option!
				if output and verbose:
					print(("git gc: %s" % (output,)), file=sys.stderr)

				output = RunCommand(["git",
						     "--git-dir=%s" % (GitDir,),
						     "--work-tree=%s" % (os.path.dirname(GitDir),),
						     "checkout", "--progress",
						     IMPORT_REF.rsplit('/', 1)[1], "--", "."])
				if output and verbose:
					print(("git checkout: %s" % (output,)), file=sys.stderr)


	def ProgressMsg(self, msg):
		"""Emit a progress message for the user."""
		sys.stderr.write(msg)

	def Progress(self, done, items):
		"""Inform the user of our current progress."""
		percent = (100.0 * float(done)) / float(items)
		if done == items:
			tail = " done\n"
		else:
			tail = ""

		msg = "\r %3.0f%% (%d/%d)%s" % (percent, done, items, tail,)
		self.ProgressMsg(msg)

	def BeginCommit(self, delta, parent):
		"""Start a new commit (having the indicated parent)."""
		mark = self.GetNextMark()
		self.Write("commit %s\nmark :%d\n" % (IMPORT_REF, mark,))

		# include an "original-oid" in the stream
		#
		# "fast-import will simply ignore this directive, but filter
		# processes which operate on and modify the stream before
		# feeding to fast-import may have uses for this information"
		#
		# Git's commit a965bb31166d04f3e5c8f7a93569fb73f9a9d749 added
		# support for # original-oid in git-fast-import, and "git tag
		# --contains a965bb31" tells me this will be v2.21.0 or newer:
		#
		if tuple(GitVer.split(".")) >= tuple("2.21.0".split(".")):
			self.Write("original-oid %s-%s-%s\n"
				   % (delta._sccsfile._filename, delta._sid, delta._seqno))

		ts = delta.GitTimestamp()
		self.Write("committer %s %s\n"
			   % (delta._ui.email, ts))

		self.WriteData(delta.GitComment())
		if parent:
			self.Write("from :%d\n" % (parent,))

		return mark

	def WriteTag(self, pdelta, parent):
		"""Write a new Tag for the new SID level."""
		# we're tagging the previous release each time we see a new one
		relno = pdelta.SidLevel() - 1
		tag = ("v%d" % (relno,))
		trev = 0
		# add a tag "revision" number to avoid cases of "error: multiple
		# updates for ref 'refs/tags/v18' not allowed" when release
		# levels are not consistently incremented at release time....
		if tag in self._used_tags:
			self._used_tags[tag] += 1
			trev = self._used_tags[tag]
			tag = ("v%d.%d" % (pdelta.SidLevel(), trev,))
		else:
			self._used_tags[tag] = trev

		if verbose:
			self.ProgressMsg("\nNEW Tag: %s (for %s: %s)\n"
					 % (tag, pdelta._sid, pdelta._comment.rstrip(),))

		self.Write("tag %s\n" % (tag,))
		self.Write("from :%d\n" % (parent,))
		ts = pdelta.GitTimestamp()
		self.Write("tagger %s %s\n"
			   % (pdelta._ui.email, ts))
		self.WriteData(pdelta.GitComment())

	def Filedelete(self, sfile):
		"""Write a filedelete section of a commit."""
		self.Write("D %s\n" % (sfile.gitname,))

	def Filemodify(self, sfile, body):
		"""Write a filemodify section of a commit."""
		self.Write("M %s inline %s\n" % (sfile.gitmode, sfile.gitname,))
		self.WriteData(body, enc=False)

	def CompleteCommit(self):
		"""Write the final part of a commit."""
		self.Write("\n")


# TODO: if the fuzzy commit logic puts subsequent deltas into the same
# commit, the timestamp of the commit is that of the first delta.
# One could argue that the timestamp of the last one would be a better choice.


def ImportDeltas(imp, deltas):
	if not deltas:
		raise ImportFailure("No deltas to import")
	first_delta_in_commit = None
	done = 0
	imp.ProgressMsg("\nCreating commits...\n")
	plevel = None
	parent = None
	pdelta = None
	commit_count = 0
	write_tag_next = False
	for d in deltas:
		imp.Progress(done, len(deltas))
		done += 1
		# Figure out if we need to start a new commit.
		if first_delta_in_commit:
			if not first_delta_in_commit.SameFuzzyCommit(d):
				imp.CompleteCommit()
				first_delta_in_commit = None
				if DoTags and write_tag_next:
					imp.WriteTag(plevel, current - 1)
					write_tag_next = False

				if plevel and d.SidLevel() > plevel.SidLevel() and d.SidRev() == 1:
					write_tag_next = True

		if first_delta_in_commit is None:
			first_delta_in_commit = d
			current = imp.BeginCommit(d, parent)
			commit_count += 1
			parent = current
			if pdelta:
				plevel = d

		pdelta = d

		# We're now in a commit.  Emit the body for this delta.
		body = GetBody(d._sccsfile._filename, d._seqno, EXPAND_KEYWORDS)
		if len(body) == 0:
			imp.Filedelete(d._sccsfile)
		else:
			imp.Filemodify(d._sccsfile, body)

	# Finished looping over deltas
	if parent:
		imp.CompleteCommit()

	imp.Progress(done, len(deltas))
	imp.ProgressMsg("\nDone.\n")
	print(("%d SCCS deltas in %d git commits"
			     % (len(deltas), commit_count)), file=sys.stderr)


def Import(filenames, stdout):
	"""Import the indicated SCCS files into git."""
	for filename in filenames:
		if not os.access(filename, os.R_OK):
			msg = "%s is not readable" % (filename,)
			raise ImportFailure(msg)
		if not os.path.isfile(filename):
			msg = "%s is not a file" % (filename,)
			raise ImportFailure(msg)

	sccsfiles = []
	done = 0
	imp = GitImporter()
	imp.ProgressMsg("Reading metadata from SCCS files...\n")
	for filename in filenames:
		try:
			imp.Progress(done, len(filenames))
			if IsValidSccsFile(filename):
				sf = SccsFile(filename)
				sccsfiles.append(sf)
			else:
				NotImporting(filename, None, "not a valid SCCS file")

			done += 1
		except ImportFailure:
			msg = ("\nAn import failure occurred while processing %s"
			       % (filename,))
			print(msg, file=sys.stderr)
			raise

	imp.Progress(done, len(filenames))

	# Now we have all the metadata; sort the deltas by timestamp
	# and import the deltas in time order.
	#
	delta_list = [delta for sfile in sccsfiles for delta in sfile.deltas]
	delta_list.sort(key=attrgetter('_timestamp'))

	if stdout:
		imp.SendToStdout()
	else:
		imp.StartImporter()

	try:
		ImportDeltas(imp, delta_list)
	finally:
		imp.Done()


def IsValidGitDir(path):
	"""Returns True IFF path is a valid git repo.

	Copied from git-p4.
	"""
	if (os.path.exists(path + "/HEAD")
		and os.path.exists(path + "/refs")
		and os.path.exists(path + "/objects")):
		return True;
	return False


def FindGitDir(gitdir, init):
	"""Locate the git repository."""
	if not gitdir:
		gitdir = RunCommand(["git", "rev-parse", "--git-dir"])
		if gitdir:
			gitdir = gitdir.strip()
		else:
			cdup = RunCommand(["git", "rev-parse", "--show-cdup"])
			if cdup:
				gitdir = os.path.abspath(cdup.strip())
			else:
				gitdir = "."

	if init:
		# Do a sanity check that we're not about to create /.git.
		assert gitdir
		if not os.path.exists(gitdir):
			try:
				os.mkdir(gitdir)
			except:
				raise ImportFailure("%s: Unable to create directory"
						    % (gitdir,))

		if not gitdir.endswith("/.git"):
			gitdir += "/.git"

		if IsValidGitDir(gitdir):
			raise ImportFailure("Git repository %s was already initialised"
					    % (gitdir,))
		else:
			msg = ("Initializing repository: git --git-dir=%s init"
			       % (gitdir,))
			print(msg, file=sys.stderr)
			output = RunCommand(["git", "--git-dir=%s" % (gitdir,), "init"])
			if output and verbose:
				print(("git init: %s" % (output,)), file=sys.stderr)

	if not IsValidGitDir(gitdir):
		gitdir += "/.git"
		if not IsValidGitDir(gitdir):
			raise ImportFailure("cannot locate git repository at %s"
					    % (gitdir,))

	print(("git repository: %s"
			     % (gitdir,)), file=sys.stderr)

	return gitdir


def MakeDirWorklist(dirs):
	result = []
	for dirname in dirs:
		# XXX it would be good to be able to report errors herein,
		# especially permission denied, etc....
		for root, subdirs, files in os.walk(dirname):
			for f in files:
				if f.startswith("s."):
					physpath = os.path.join(root, f)
					if os.access(physpath, os.R_OK):
						result.append(physpath)

	if not result:
		print(("Warning: No SCCS files were found in %s"
				     % (" ".join(dirs))), file=sys.stderr)
	return result


def GetTimezone(tz):
	if tz[0] == '+' or tz[0] == '-':
		assert int(tz)
		# Construct a timezone with a fixed offset from a string like "-0800"
		return timezone(timedelta(hours=int(tz[:3]), minutes=int(tz[0] + tz[3:5])))
	else:
		# Otherwise, look up the tzinfo timezone by name (like "US/Pacific")
		return ZoneInfo(tz)

# The author map should match the format of git-cvsimport:
#
# XXX currently the [time/zone] option requires the ISO8601 basic format,
# i.e. "[+-]hhmm", e.g. "-0800".
#
# <username>=[Full Name] <email@addre.ss> <zone offset or name>
#
# The email address must be surrounded by literal angle brackets
#
# e.g.:
#
#	exon=Andreas Ericsson <ae@op5.se>
#	spawn=Simon Pawn <spawn@frog-pond.org> -0400
#	bob=<bob@example.net> US/Pacific
#
# Comment lines, beginning with a '#', are ignored.
#
class UserInfo():
	def __init__(self, login, email, tz):
		self.login = login
		self.email = email
		self.tz = tz
		#print(('UserInfo: "%s" "%s" "%s"' % (self.login,self.email,self.tz)), file=sys.stderr)

def GetAuthorMap(filename):
	map = {}
	with open(filename, 'r') as fd:
		for line_no, line in enumerate(fd, 1):
			if line[0] == '#':
				continue
			m = re.fullmatch(r"\s*(?P<key>[^=\s]+)\s*=\s*(?:(?P<login>.*\S)\s+)?"
			 r"(?P<email><[^<>\s]*>)\s*(?:(?<=\s)(?P<tz>[^\s]+)\s*)?", line)
			if not m:
				raise UsageError('Invalid syntax in author map at line %d: "%s"'
				 % (line_no, line.rstrip('\n')))
			map[m['key']] = UserInfo(m['key'],
			 m['login'] + ' ' + m['email'] if m['login'] else m['email'],
			 GetTimezone(m['tz']) if m['tz'] else None)

	return map

def GitUser(username, login_name, mail_domain):
	# xxx actually username is optional to git-fast-import too!
	if mail_domain:
		return "%s <%s@%s>" % (username, login_name, mail_domain,)
	return "%s <%s>" % (username, login_name,)

def GetUserInfo(login_name, mail_domain, tz):
	"""Get a user's info corresponding to the given login name."""
	if AuthorMap and (am := AuthorMap.get(login_name)):
		return am
	try:
		gecos = pwd.getpwnam(login_name).pw_gecos
	except:
		if verbose:
			print(("%s: unknown login" % (login_name,)), file=sys.stderr)

		return UserInfo(login_name,
				GitUser(login_name, login_name, mail_domain),
				tz)
	username = gecos.split(",")[0]
	username.replace("&", login_name.capitalize())
	return UserInfo(login_name, GitUser(username, login_name, mail_domain), tz)

def ParseOptions(argv):
	global IMPORT_REF
	global MAIL_DOMAIN
	global FUZZY_WINDOW
	global EXPAND_KEYWORDS
	global DEFAULT_USER_TZ
	global MoveDate
	global MoveZone
	global DoTags
	global verbose
	global AuthorMap

	AuthorMap = None
	MoveDate = None
	MoveZone = None

	parser = optparse.OptionParser()
	parser.add_option("--branch",
			  help="branch to populate",
			  default="master")
	parser.add_option("--maildomain",
			  help="Mail domain for usernames taken from SCCS files")
	parser.add_option("--tz",
			  help="Default timezone name or UTC offset for timestamps (default local time)")
	parser.add_option("--authormap",
			  help="File mapping author user-IDs to Git style user.{name,email}")
	parser.add_option("--dirs",
			  action="store_true",
			  help=("Command-line arguments are a list "
				"of directories to automatically search "
				"rather than a list of SCCS files"))
	parser.add_option("--expand-kw", default=False, action="store_true",
			  help="Expand keywords")
	parser.add_option("--fuzzy-commit-window",
			  default=FUZZY_WINDOW,
			  help=("Deltas more than this many seconds apart "
				"are always considered to be in different commits"))
	parser.add_option("--git-dir",
			  help="Directory containing the git repository")
	parser.add_option("--init", default=False, action="store_true",
			  help="Initialise the git repository first")
	parser.add_option("--move-date",
			  help=("set the date SCCS files moved between timezones"
				" (in ISO8601 form: YYYY/MM/DDTHH:MM:SS)"))
	parser.add_option("--move-zone",
			  help=("Set the new timezone after --move-date"))
	parser.add_option("--no-tags", default=False, action="store_true",
			  help="Don't try to create tags on SID level bumps.")
	parser.add_option("--stdout", default=False, action="store_true",
			  help=("Send git-fast-import data to stdout "
				"rather than to git-fast-import"))
	parser.add_option("--use-sccs", default=False, action="store_true",
			  help=("Use the 'sccs' front-end for SCCS commands"
				" (by default need for 'sccs' is auto-detected)"))
	parser.add_option("--debug", default=False, action="store_true",
			  help="Print all commands being run and any stderr output.")
	parser.add_option("--verbose", default=False, action="store_true",
			  help="Print more verbose status messages.")

	(options, args) = parser.parse_args(argv)

	EXPAND_KEYWORDS = options.expand_kw
	verbose = options.verbose

	if options.maildomain:
		MAIL_DOMAIN = options.maildomain

	if options.tz:
		# xxx verify it is in the correct format!
		DEFAULT_USER_TZ = GetTimezone(options.tz)

	if options.no_tags:
		DoTags = False

	if options.use_sccs:
		GET = "sccs get"
		PRS = "sccs prs"
		VAL = "sccs val"

	if options.move_date:
		if not options.move_zone:
			raise UsageError("--move-date requires --move-zone")
		try:
			MoveDate = datetime.strptime(options.move_date,
							      '%Y/%m/%dT%H:%M:%S')
			# --move-date is specified in the pre-move zone
			# Convert this to an aware datetime, either in local or --tz zone
			if DEFAULT_USER_TZ is None:
				MoveDate = MoveDate.astimezone()
			else:
				MoveDate = MoveDate.replace(tzinfo=DEFAULT_USER_TZ)
		except:
			raise UsageError("Bad --move-date")
		try:
			MoveZone = GetTimezone(options.move_zone)
		except:
			raise UsageError("Bad --move-zone")

	if options.authormap:
		AuthorMap = GetAuthorMap(options.authormap)

	try:
		FUZZY_WINDOW = float(options.fuzzy_commit_window)
	except ValueError:
		raise UsageError("The argument for the --fuzzy-commit-window option "
				 "should be a number, but you specified '%s'"
				 % (options.fuzzy_commit_window,))
	IMPORT_REF = "refs/heads/%s" % (options.branch,)
	return options, args


def main(argv):
	global progname
	progname = argv[0] or "git-sccsimport"

	global GitDir
	global GitVer
	GitVer = RunCommand(["git", "--version"]).split(" ")[-1]

	global GET
	global PRS
	global VAL
	try:
		RunCommand("prs".split(" "))
	except ImportFailure:
		GET = "get"
		PRS = "prs"
		VAL = "val"
	except OSError:
		GET = "sccs get"
		PRS = "sccs prs"
		VAL = "sccs val"

	try:
		options, args = ParseOptions(argv)
		#print(("Positional args:", " ".join(args)), file=sys.stderr)
		args = args[1:]
		if not args:
			if options.dirs:
				raise UsageError("You did not specify any directories to import from")
			else:
				raise UsageError("You did not specify any SCCS files to import")

		if options.stdout and options.init:
			raise UsageError("The --init option is incompatible "
					 "with the --stdout option")

		if not options.stdout:
			try:
				GitDir = FindGitDir(options.git_dir, options.init)
				os.environ["GIT_DIR"] = GitDir
			except ImportFailure(init_failure):
				if options.init:
					action = "Initialisation"
				else:
					action = "Locate"

				print(("%s failed:\n%s" % (action, init_failure,)), file=sys.stderr)
				return 1

		if options.dirs:
			items = MakeDirWorklist(args)
		else:
			items = args

		if len(items) <= 0:
			print("No items to import!", file=sys.stderr)
			return 1

		if debug:
			print(("Importing %d items:" % (len(items),), " ".join(items)), file=sys.stderr)
		else:
			print(("Importing %d items..." % (len(items),)), file=sys.stderr)

		return Import(items, options.stdout)

	except UsageError as usage_err:
		return Usage(progname, 2, sys.stderr, usage_err)
	except ImportFailure as imp_failure:
		print(("Import failed: %s" % (imp_failure,)), file=sys.stderr)
		return 1

def using(point=""):
	usage=resource.getrusage(resource.RUSAGE_SELF)
	return '''%s: usertime=%s systime=%s maxrss=%s''' % (point, usage[0], usage[1], usage[2])

if __name__ == '__main__':
	rc = main(sys.argv)
	print(using(progname), file=sys.stderr)
	sys.exit(rc)

# Local Variables:
# eval: (make-local-variable 'compile-command)
# compile-command: (concat "cp ./" (file-name-nondirectory (buffer-file-name)) " $HOME/bin/" (file-name-sans-extension (file-name-nondirectory (buffer-file-name))))
# End:
