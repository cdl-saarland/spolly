import time
import subprocess as sub

statSurround = "===-------------------------------------------------------------------------===\n"
statCenter   = "                          ... Statistics Collected ...\n"

class StatParser(object):

  def __init__(self):
    pass

  " Main method for interaction with a StatParser "
  def parseFile(self, filename):
    fd = open(filename, "r")
    
    firstline = fd.readline()
    parts     = firstline.strip().split(" ")
    args      = " ".join(parts[2:])
    version   = sub.check_output("%s --version; exit 0" % (parts[1]), shell=True)
    
    statistics = None
    found = 0
    for line in fd:
      if not found and line == statSurround:
        found += 1
      elif found == 1 and line == statCenter:
        found += 1
      elif found == 2 and line == statSurround:
        found += 1
      elif found == 3:
        statistics = self.parseStatistics(fd)
      else:
        found = 0

    currentTime = time.asctime(time.localtime(time.time()))

    #print currentTime
    #print args
    #print version
    #print statistics
    return statistics
    
  def parseStatistics(self, fd):
    statistics = []
    for line in fd:
      line = line.strip().replace("\t"," ")
      while "  " in line:
        line = line.replace("  "," ")
      if not line: 
        continue

      # Number PassName - Message in words
      parts    = line.split(" ")
      count    = int(parts[0])
      passname = parts[1]
      message  = " ".join(parts[3:])
      
      statistics.append((count, passname, message))

    return statistics

  #def 
    #tmpfile = tempfile.mkstemp


sp = StatParser()
sp.parseFile("/home/johannes/git/sambamba/testdata/test")
