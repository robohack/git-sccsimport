#!/usr/bin/env python
#
# git-sccsimport.py -- Imports SCCS files into git
#
# Author: James Youngman <jay@gnu.org>
# Copyright: 2008 James Youngman <jay@gnu.org>
# License: GNU GPL version 2 or later <http://www.gnu.org/licenses/old-licenses/gpl-2.0.html>
#
"""
A fast git importer for SCCS files.

How to use this program:

Let's assume you have some SCCS files in $PROJECTDIR and want to
convert them to a git repository in the directory $NEWGIT.

First, make sure the SCCS (or CSSC) binaries are on your $PATH.  Then
do this:

  cd "$PROJECTDIR"
  python git-sccsimport.py --init --git-dir="$NEWGIT" --dirs .

Notice that git-sccsimport is being run with its working
directory as the root of the tree of SCCS files.  This is
becaue the relative path from your working directory to the
SCCS file is also used as the name of the file in the resulting
git repository.

I tried this on a 32M code repository in SCCS and it produced a
36M git repository. 
"""
import datetime
import errno
import optparse
import os
import os.path
import re
import stat
import subprocess
import sys
import time

GET = "get"
PRS = "prs"
SCCS_ESCAPE = chr(1)
TIMEZONE = None
MAIL_DOMAIN = None
UNIX_EPOCH = time.mktime(datetime.datetime(1970, 1, 1,
											0, 0, 0, 0,
											None).timetuple())
IMPORT_REF = None


# Two checkins separated by more than FUZZY_WINDOW
# will never be considered part of the same commit.
FUZZY_WINDOW = 300.0


verbose = False


class ImportFailure(Exception):
  pass

class UsageError(Exception):
  pass

class AbstractClassError(Exception):
  pass

def Usage(who, retval, f, e):
  if e:
	 print >>f, e
  print >>f, ("usage: %s sccs-file [sccs-file...]"
			   % (who,))
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
  print >> sys.stderr, msg


def DiagnoseCommandFailure(command, returncode, errors):
  if not errors:
	 errors = ""
  if returncode < 0:
	 msg = ("%s %s killed by signal %s" % command, -(returncode))
  else:
	 msg = ("%s %s returned exit status %s" % command, returncode)
  raise ImportFailure, "%s\n%s" % (errors, msg)
	 

def RunCommand(commandline):
  try:
	 if verbose:
	   msg = ("Running command: %s\n"
			  % (" ".join(commandline),))
	   sys.stderr.write(msg)
	 child = subprocess.Popen(commandline,
							  close_fds = True,
							  stdin =subprocess.PIPE,
							  stdout=subprocess.PIPE,
							  stderr=subprocess.PIPE)
	 output, errors = child.communicate(None)
	 if child.returncode != 0:
	   # Some stderr output is normal (warnings, etc.)
	   DiagnoseCommandFailure(commandline[0], child.returncode, errors)
	 else:
	   return output
  except OSError, oe:
	 msg = ("Failed to run '%s': %s (%s)"
			% (commandline[0], oe,
			   errno.errorcode[oe.errno]))
	 raise ImportFailure, msg
		 

	 

def GetBody(sfile, seqno, expand_keywords):
  options = [GET, "-p", "-s", ("-a%d" % seqno)]
  if not expand_keywords:
	 options.append("-k")
  options.append(sfile)
  return RunCommand(options)
	 

def FileMode(filename):
  return stat.S_IMODE(os.stat(filename).st_mode)


class SccsFileQueryBase(object):
  @staticmethod
  def HeaderLines(filename):
	 header_end = "^%cT" % (SCCS_ESCAPE,)
	 result = []
	 try:
	   f = open(filename, "rb")
	   for line in f.readlines():
		 if line.startswith(header_end):
		   break
		 else:
		   result.append(line)
	   return result
	 finally:
	   f.close()

		 

#class SccsFileQuerySlow(SccsFileQueryBase):
#	"""Extract information from SCCS files by running prs."""
#	@staticmethod
#	def RunPrs(options):
#	  commandline = [PRS]
#	  commandline.extend(options)
#	  return RunCommand(commandline)
#	
#	@staticmethod
#	def FetchDeltaProperties(sid, filename):
#	  fmt = (":Dy:/:Dm:/:Dd:%(esc)c"  # 0 delta creation date
#			 ":Th:::Tm:::Ts:%(esc)c"  # 1 delta creation time (24h)
#			 ":C:%(esc)c"			  # 2 checkin comments
#			 ":DS:%(esc)c"			  # 3 seqno
#			 ":DP:%(esc)c"			  # 4 parent seqno
#			 ":DT:%(esc)c"			  # 5 delta type (R or D)
#			 ":I:%(esc)c"			  # 6 SID
#			 ":MR:%(esc)c"			  # 7 MR numbers
#			 ":P:%(esc)c"			  # 8 Perpetrator (committer)
#			 % { 'esc': SCCS_ESCAPE })
#	  cmdline = [("-d%s" % fmt), ("-r%s" % sid), filename]
#	  propdata = SccsFileQuerySlow.RunPrs(cmdline)
#	  return propdata.split(SCCS_ESCAPE)
#
#	@staticmethod
#	def IsValidSccsFile(filename):
#	  try:
#		output = SccsFileQuerySlow.RunPrs(["-d:F: ", filename])
#		return True
#	  except ImportFailure:
#		return False
#	  
#	@staticmethod
#	def GetRevisionList(filename):
#	  revisions = SccsFileQuerySlow.RunPrs(["-d:I: ", "-e", filename])
#	  return revisions.split()


class SccsFileQueryFast(SccsFileQueryBase):
  """Extract information from SCCS files by parsing them directly."""
  DELTA_RE = re.compile("^%cd D ([.0-9]*)" % (SCCS_ESCAPE,))

  @staticmethod
  def IsValidSccsFile(filename):
	 try:
	   f = open(filename, "rb")
	   header = f.read(2)
	   return header[0] == SCCS_ESCAPE and header[1] == 'h'
	 finally:
	   f.close()

  @staticmethod
  def GetRevisionList(filename):
	 result = []
	 header_end = "^%cT" % (SCCS_ESCAPE,)
	 for line in SccsFileQueryBase.HeaderLines(filename):
	   m = SccsFileQueryFast.DELTA_RE.match(line)
	   if m:
		 result.append(m.group(1))
	 return result

  @staticmethod
  def FetchDeltaProperties(sid, filename):
	 found = False
	 props = []
	 comments = []
	 comment_leader = "%cc" % (SCCS_ESCAPE,)
	 for line in SccsFileQueryBase.HeaderLines(filename):
	   if not found:
		 m = SccsFileQueryFast.DELTA_RE.match(line)
		 if m and (sid == m.group(1)):
		   found = True
		   fields = line.split()
		   props = [ fields[3],
					 fields[4],
					 None, # checkin comment
					 fields[6],
					 fields[7],
					 'D',
					 fields[2],
					 "",	   # MR list
					 fields[5],
					 "yodel"
					 ]
		   continue
		 else:
		   if found:
			 if line.startswith(comment_leader):
			   comments.append(line[3:])
			 else:
			   break
	 if found:
	   props[2] = "\n".join(comments)
	   # print >> sys.stderr, "props: %s" % (props,)
	   return props
	 else:
	   return None


def SccsFileQuery():
  """Factory method for objects that query SccsFileQuery objects"""
  return SccsFileQueryFast()


class Delta(object):
  """Represents the properties of an SCCS delta that we
  import into git."""
  def __init__(self, sccsfile, sid, qif, *args, **kwargs):
	 super(Delta, self).__init__(*args, **kwargs)
	 self._sccsfile = sccsfile
	 self._sid		= sid
	 self._qif = qif
	 self.FetchDeltaProperties()

  def __repr__(self):
	 return 'Delta(%s, "%s")' % (repr(self._sccsfile), self._sid)

  def FetchDeltaProperties(self):
	 """Query the properties of this delta from the SCCS file."""
	 props = self._qif.FetchDeltaProperties(self._sid,
											self._sccsfile._filename)
	 assert len(props)>1, "%s %s %s" % (self._sccsfile._filename, self._sid, props)
	 self.SetTimestamp(props[0], props[1])
	 (self._comment, self._seqno, self._parent_seqno, self._type,
	  sidcheck, mrlist, self._comitter, _) = props[2:]
		 
	 self._seqno = int(self._seqno)
	 self._parent_seqno = int(self._parent_seqno)
	 if self._comment == "\n":
		 self._comment = None
	 assert sidcheck==self._sid
	 self._mrs = mrlist.split()

  def SameFuzzyCommit(self, other):
	 #print >>sys.stderr, ("SameFuzzyCommit: comparing\n1: %s with\n2: %s"
	 #					   % (self, other))
	 if self._comment != other._comment:
	   return False
	 elif self._comitter != other._comitter:
	   return False
	 elif self._mrs != other._mrs:
	   return False
	 else:
	   delta = abs(other._timestamp - self._timestamp)
	   if delta > FUZZY_WINDOW:
		 return False
	   else:
		 return True

  def SetTimestamp(self, checkin_date, checkin_time):
	   try:
		 year, month, monthday = [int(f) for f in checkin_date.split("/")]
	   except ValueError:
		 raise ImportFailure, ("Unexpected date format: %s"
							   % (checkin_date,))
	   try:
		 h,m,s = [int(f) for f in checkin_time.split(":")]
	   except ValueError:
		 raise ImportFailure, ("Unexpected time format: %s"
							   % (checkin_time,))
	   microsec = 0

	   if year < 100:
		 # Apply the y2k rule (see the "Year 2000 Issues" section
		 # of the CSSC documentation).
		 if year < 69:
		   year += 2000
		 else:
		   year += 1900

	   dt = datetime.datetime(year, month, monthday,
							  h, m, s,
							  microsec, TIMEZONE)
	   epoch_offset = time.mktime(dt.timetuple())
	   # We subtract UNIX_EPOCH to take account of the fact
	   # that the system epoch may in fact not be the same as the Unix
	   # epoch.	 git fast-import requires the timestamp to be measured in
	   # seconds since the Unix epoch.
	   self._timestamp = epoch_offset - UNIX_EPOCH
		 
  def GitTimestamp(self):
	 n = int(self._timestamp)
	 return "%d +0000" % (n,)


class SccsFile(object):
  def __init__(self, name, *args, **kwargs):
	 super(SccsFile, self).__init__(*args, **kwargs)
	 self._filename = name
	 qif = SccsFileQuery()
	 revisions = filter(self.GoodRevision, qif.GetRevisionList(name))
	 self._deltas = [Delta(self, sid, qif) for sid in revisions]
	 self._gitname = self.GitFriendlyName(self._GottenName())
	 if FileMode(self._filename) & 0111:
	   self._gitmode = "755"
	 else:
	   self._gitmode = "644"
	 
  gitname = property(lambda self: self._gitname)
  gitmode = property(lambda self: self._gitmode)
  filename = property(lambda self: self._filename)

  @staticmethod
  def IsValidSccsFile(filename):
	 qif = SccsFileQuery()
	 return qif.IsValidSccsFile(filename)

  def __repr__(self):
	 return "SccsFile(r'%s')" % self._filename

  @staticmethod
  def GitFriendlyName(name):
	 """git-fastimport does not like leading or trailing slashes,
	 or . or .. in file names.	This method removes such things."""
	 if os.path.isabs(name):
	   raise ImportFailure, "%s is an absolute path name" % (name,)
	 drive, path = os.path.splitdrive(name)
	 return os.path.normpath(path)

  def _GottenName(self):
	 """Convert the name of an SCCS file to the name of the
	 working file as would be assumed by make.	Specifically,
	 the s. prefix is stipped, and if the s.file is in a directory
	 called SCCS, that directory is stripped out of the path also.
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
	 if len(comps) > 1:
	   return True
	 else:
	   NotImporting(self._filename, sid,
					"SID contains no level component")
	   return False

		 
		 

class GitImporter(object):
  """Handles communications with git-fast-import."""
  
  def __init__(self, *args, **kwargs):
	 super(GitImporter, self).__init__(*args, **kwargs)
	 self._next_mark = 1
	 self._command = None
	 self._importer = None
	 self._write_to_stdout = False

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

  def Write(self, s):
	 """Write some data to the importer."""
	 if self._write_to_stdout:
	   sys.stdout.write(s)
	 else:
	   assert self._importer
	   self._importer.stdin.write(s)
	   
  def Done(self):
	 if self._importer:
	   self._importer.stdin.close()
	   returncode = self._importer.wait()
	   if returncode != 0:
		 DiagnoseCommandFailure(self._command, returncode, None)
	   else:
		 print >>sys.stderr, ("%s completed successfully"
							  % (self._command,))
		 
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
	 msg = "\r %3.0f%% (%d/%d)%s" % (percent, done, items, tail)
	 self.ProgressMsg(msg)

  def GetUserEmailAddress(self, login_name):
	 """Get an email address corresponding to the given login name."""
	 if MAIL_DOMAIN:
	   return "%s@$s" % (login_name,MAIL_DOMAIN)
	 else:
	   return login_name

  def WriteData(self, data):
	 """Emit a data command followd by a blob of data."""
	 self.Write("data %d\n" % (len(data),))
	 self.Write(data)
	 self.Write("\n")
			 
  def BeginCommit(self, delta, parent):
	 """Start a new commit (having the indicated parent)."""
	 mark = self.GetNextMark()
	 self.Write("commit %s\nmark :%d\n" % (IMPORT_REF, mark))
	 ts = delta.GitTimestamp()
	 self.Write("committer %s <%s> %s\n"
				% (delta._comitter,
				   self.GetUserEmailAddress(delta._comitter),
				   ts))
	 if delta._comment:
	   self.WriteData(delta._comment)
	 else:
	   self.WriteData("")		   # commit comment is mandatory
	 if parent:
	   self.Write("from :%d\n" % (parent,))
	 return mark

  def Filemodify(self, sfile, body):
	 """Write a filemodify section of a commit."""
	 self.Write("M %s inline %s\n" % (sfile.gitmode, sfile.gitname))
	 self.WriteData(body)

  def CompleteCommit(self):
	 """Write the final part of a commit."""
	 self.Write("\n")
		 
# TODO: if the fuzzy commit logic puts subsequent deltas into the same
# commit, the timestamp of the commit is that of the first delta.	One
# could argue that the timestamp of the last one would be a better
# choice.

def ImportDeltas(imp, deltas):
  if not deltas:
	 raise ImportFailure, "No deltas to import"
  first_delta_in_commit = None
  done = 0
  imp.ProgressMsg("Creating commits...\n")
  parent = None
  commit_count = 0
  for d in deltas:
	 imp.Progress(done, len(deltas))
	 done += 1
	 # Figure out if we need to start a new commit.
	 if first_delta_in_commit:
	   if not first_delta_in_commit.SameFuzzyCommit(d):
		 imp.CompleteCommit()
		 first_delta_in_commit = None
	 if first_delta_in_commit is None:
	   first_delta_in_commit = d
	   current = imp.BeginCommit(d, parent)
	   commit_count += 1
	   parent = current
	 # We're now in a commit.  Emit the body for this delta.
	 body = GetBody(d._sccsfile._filename, d._seqno, False)
	 imp.Filemodify(d._sccsfile, body)
  # Finished looping over deltas
  if parent:
	   imp.CompleteCommit()
  imp.Progress(done, len(deltas))
  print >>sys.stderr, ("%d SCCS deltas in %d git commits"
						% (len(deltas), commit_count))


def Import(filenames, stdout):
  """Import the indicated SCCS files into git."""
  for filename in filenames:
	 if not os.access(filename, os.R_OK):
	   msg = "%s is not readable" % (filename,)
	   raise ImportFailure, msg
	 if not os.path.isfile(filename):
	   msg = "%s is not a file" % (filename,)
	   raise ImportFailure, msg
  sccsfiles = []
  done = 0
  imp = GitImporter()
  imp.ProgressMsg("Reading metadata from SCCS files...\n")
  for filename in filenames:
	 try:
	   imp.Progress(done, len(filenames))
	   if SccsFile.IsValidSccsFile(filename):
		 sf = SccsFile(filename)
		 sccsfiles.append(sf)
	   else:
		 NotImporting(filename, None, "not a valid SCCS file")
	   done += 1
	 except ImportFailure:
	   msg = ("\nAn import failure occurred while processing %s"
			  % (filename,))
	   print >> sys.stderr, msg
	   raise
  imp.Progress(done, len(filenames))
  # Now we have all the metadata; sort the deltas by timestamp
  # and import the deltas in time order.
  delta_list = []
  for sfile in sccsfiles:
	 for delta in sfile._deltas:
	   ts = "%15f" % (delta._timestamp,)
	   t = (ts, delta)
	   delta_list.append(t)
  delta_list.sort()

  if stdout:
	 imp.SendToStdout()
  else:
	 imp.StartImporter()
  try:
	 ImportDeltas(imp, [d[1] for d in delta_list])
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
	 if not gitdir.endswith("/.git"):
	   gitdir += "/.git"
	 if IsValidGitDir(gitdir):
	   raise ImportFailure, ("Git repository %s was already initialised"
							 % (gitdir,))
	 else:
	   RunCommand(["git", "--git-dir=%s" % (gitdir,), "init"])
	   
  if not IsValidGitDir(gitdir):
	 gitdir += "/.git"
	 if not IsValidGitDir(gitdir):
	   raise ImportFailure, ("cannot locate git repository at %s" %
							 (gitdir,))
  print >> sys.stderr, "git repository is at", gitdir
  return gitdir


def MakeDirWorklist(dirs):
  result = []
  for dirname in dirs:
	 for root, subdirs, files in os.walk(dirname):
	   for f in files:
		 if f.startswith("s."):
		   physpath = os.path.join(root, f)
		   if os.access(physpath, os.R_OK):
			 result.append(physpath)
  if not result:
	 print >>sys.stderr, ("Warning: No SCCS files were found in %s"
						  % (" ".join(dirs)))
  return result


def ParseOptions(argv):
  global IMPORT_REF
  global MAIL_DOMAIN
  global FUZZY_WINDOW
  global verbose
  parser = optparse.OptionParser()
  parser.add_option("--branch",
					 help="branch to populate",
					 default="master")
  parser.add_option("--maildomain",
					 help="Mail domain for usernames taken from SCCS files")
  parser.add_option("--fuzzy-commit-window",
					 default=FUZZY_WINDOW,
					 help=("Deltas more than this many seconds apart "
						   "are always considered to be in different commits"))
  parser.add_option("--git-dir",
					 help="Directory containing the git repository")
  parser.add_option("--init", default=False, action="store_true",
					 help="Initialise the git repository first")
  parser.add_option("--verbose", default=False, action="store_true",
					 help="Print verbose status messages")
  parser.add_option("--stdout", default=False, action="store_true",
					 help=("Send git-fast-import data to stdout "
						   "rather than to git-fast-import"))
  parser.add_option("--dirs",
					 action="store_true",
					 help=("Command-line arguments are a list "
						   "of directories to automatically search "
						   "rather than a list of SCCS files"))
  (options, args) = parser.parse_args(argv)
  verbose = options.verbose
  if options.maildomain:
	 MAIL_DOMAIN = options.maildomain
  try:
	 FUZZY_WINDOW = float(options.fuzzy_commit_window)
  except ValueError:
	 raise UsageError("The argument for the --fuzzy-commit-window option "
					  "should be a number, but you specified '%s'"
					  % (options.fuzzy_commit_window,))
  IMPORT_REF = "refs/heads/%s" % (options.branch,)
  return options, args


def main(argv):
  progname = argv[0] or "git-sccsimport"
  try:
	 options, args = ParseOptions(argv)
	 print >>sys.stderr, "Positional args:", " ".join(args)
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
		 os.environ["GIT_DIR"] = FindGitDir(options.git_dir, options.init)
	   except ImportFailure, init_failure:
		 if options.init:
		   action = "initialise"
		 else:
		   action = "locate"
		   print >>sys.stderr, ("Failed to %s the git repository: %s"
								% (action, init_failure))
		   return 1

	 if options.dirs:
	   items = MakeDirWorklist(args)
	 else:
	   items = args
	 print >>sys.stderr, "Importing items:", " ".join(items)
	 return Import(items, options.stdout)

  except UsageError, usage_err:
	 return Usage(progname, 1, sys.stderr, usage_err)
  except ImportFailure, imp_failure:
	 print >> sys.stderr, "Import failed: %s" % (imp_failure,)
	 return 1


if __name__ == '__main__':
  sys.exit(main(sys.argv))
