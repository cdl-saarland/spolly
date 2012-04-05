import sqlite3

class Statistic(object):
  conn = sqlite3.connect('./statistic.db3')
  conn.row_factory = sqlite3.Row
  curs = conn.cursor()

  def __init__(self):
    self.curs.execute("SELECT name FROM sqlite_master WHERE type='table'")
    print self.curs.fetchone()

s1 = Statistic()
    


