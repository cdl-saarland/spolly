import numpy as np
import matplotlib.pyplot as plt
import os

options = {"path":"../latex/Figures/", "filename":"", "grid":"y", "rotation":"-45"}

print "Input options.... (use the format of the default value!)\n"

# Collect all options
for key,value in options.items():
  new_value = raw_input("%s [%s]:" % (key, value))
  if not new_value:
    new_value = value
  options[key] = new_value

print "This options will be saved for all plots"
print "----------------------------------------\n"


# some default values
programs = []
Nbars    = 1
colors   = ['#FF0000', '#0000FF', '#00FF00', '#FFFF00', '#FF00FF', '#00FFFF', 
            '#339933', '#FF3333']

while True:
  if programs and not raw_input("Change programs? [N/y]").lower() == "y":
    pass
  else:
    # Get a list of programs (python syntax!)
    try:
      # First programs is a string
      programsStr = raw_input("Programs:").strip()
      if programsStr[0] == "[" and programsStr[-1] == "]":
        programsStr = programsStr[1:-1]
      # now a list
      programs = [n.strip() for n in programsStr.split(',')]
    except:
      print "Input should be a comma seperated list of strings... exit"
      exit()
  
    while "" in programs:
      programs.remove("")


    print "Programs are:"
    print programs
    
    # todo permute
  
  # The number of programs
  N = len(programs)

  try:
    NbarsStr = raw_input("Number of bars[%i]:" % Nbars)
    if NbarsStr:
      Nbars = int(NbarsStr)
    assert(Nbars > 0)
  except:
    print "Number of bars should be a positive integer... exit"
    exit()

  Ngabs = Nbars
  try:
    NgapsStr = raw_input("Number of gaps[%i]:" % Nbars)
    if NgapsStr:
      Ngaps = int(NgapsStr)
    assert(Ngaps >= 0)
  except:
    print "Number of gaps should be a non negative integer... exit"
    exit()

  Width = 1.0
  try:
    WidthStr = raw_input("Width per bar[%.1f]:" % Width)
    if WidthStr:
      Width = float(WidthStr)
    assert(Width > 0.0)
  except:
    print "Number of bars should be a positive float... exit"
    exit()  
  
  BarNames  = ["" for i in range(Nbars)]
  BarValues = [[] for i in range(Nbars)]
  BarColors = colors[:Nbars]

  for i in range(Nbars):
    name = raw_input("Name for bar %2i:" % i).strip()
    BarNames[i] = name
    # Use i as name if none is set (just for this script) 
    if not name:
      name = str(i)
    
    try:
      # First programs is a string
      valuesStr = raw_input("Value list for bar %s:" % name).strip()
      if valuesStr[0] == "[" and valuesStr[-1] == "]":
        valuesStr = valuesStr[1:-1]
      # now a list
      values = [n.strip() for n in valuesStr.split(',')]
      while "" in values:
        values.remove("")
      values = [float(n) for n in values]
      assert(len(values) == N)
    except:
      print "Input should be a comma seperated list with %i elements... exit" % N
      exit()

    BarValues[i] = values

    colorStr = raw_input("Color for bar %s[%s]:" % (name, BarColors[i])).strip()
    if colorStr:
      BarColors[i] = colorStr
  
  ylabel = raw_input("ylabel (empty=>None):")
  title  = raw_input("title  (empty=>None):")
  
  stepping = 1.0
  try:
    steppingStr = raw_input("Stepping[%i]:" % stepping)
    if steppingStr:
      stepping = float(steppingStr)
    assert(stepping > 0)
  except:
    print "Stepping should be a positve float... exit"
    exit()


  # enough input... lets plot a figure


  # locations on the x axis
  locs = np.arange(Ngaps * Width, N * (Nbars + Ngaps) * Width + Ngaps * Width, (Nbars+Ngaps)*Width)  
  print locs
  fig = plt.figure()
  ax = fig.add_subplot(111)
  if options["grid"] in ["y","Y"]:
    ax.grid(color='black', axis='y', linestyle='dotted', linewidth=0.5)
   
  ax.set_axisbelow(True)
  if ylabel:
    ax.set_ylabel(ylabel)
  if title:
    ax.set_title(title)

  BarRects = []
  for i in range(Nbars):
    print len(BarValues[i])
    BarRects.append(ax.bar(locs + Width * i, BarValues[i], Width, color=BarColors[i]))

  maxima  = [max(l) for l in BarValues]
  maximum = max(maxima)

  # label should be in the middle of each bar group
  ax.set_xticks(locs + (Width * (Nbars / 2.0)))
  # adjust the limits
  ax.set_xlim(0, N * (Ngaps + Nbars) * Width + Ngaps)
  maximum2 = maximum + 5
  print "\n",maximum2,"\n"
  ax.set_yticks(np.arange(0, maximum + stepping, stepping))
  maximum2 = 115
  rect =BarRects[2][7]
  height=rect.get_height()
  ax.annotate('276', xy = (rect.get_x()+rect.get_width()/2., 115), xycoords='data',
                xytext=(-60, -20), textcoords='offset points',fontsize=18,arrowprops=dict(arrowstyle="->", connectionstyle="arc3,rad=.3"))
  rect =BarRects[3][7]
  height=rect.get_height()
  ax.annotate('208', xy = (rect.get_x()+rect.get_width()/2., 115), xycoords='data',
                xytext=(30, -20), textcoords='offset points',fontsize=18,arrowprops=dict(arrowstyle="->", connectionstyle="arc3,rad=-.3"))

  ax.set_ylim(0,maximum2)
  
  rot = int(options["rotation"])
  if rot < 0:
    ax.set_xticklabels(programs, rotation=rot, ha='left')
  elif rot > 0:
    ax.set_xticklabels(programs, rotation=rot, ha='right')
  else:
    ax.set_xticklabels(programs)
 
  legend = [[], []]
  for i in range(Nbars):
    if BarNames[i]:
      legend[0].append(BarRects[i][0])
      legend[1].append(BarNames[i])
  ax.legend(legend[0], legend[1], loc=2)

  print "\nNow the size and dpi can be adjusted\n"
  dpi  = 100
  size = fig.get_size_inches()
  while True:
    print "Size in Inches:", size, " DPI:", dpi
    print "Which should result in a %i x %i Image"%(dpi*size[0], dpi*size[1])
    if raw_input("Ok?[Y/n]").lower() != "n":
      break
    else:
      try:
        dpiStr = raw_input("DPI[%i]:" % dpi)
        if dpiStr:
          dpi = int(dpiStr)
        assert(dpi > 0)
      except:
        print "DPI should be a positive integer... exit"
        exit()

      try:
        sizeXStr = raw_input("SizeX[%i]:" % size[0])
        if sizeXStr:
          size[0] = int(sizeXStr)
        assert(size[0] > 0)
      except:
        print "Size should be a positive integer... exit"
        exit()
      
      try:
        sizeYStr = raw_input("SizeY[%i]:" % size[1])
        if sizeYStr:
          size[1] = int(sizeYStr)
        assert(size[1] > 0)
      except:
        print "Size should be a positive integer... exit"
        exit()

      fig.set_size_inches(size)
  
  savename = os.path.join(options["path"], options["filename"])
  fig.savefig(savename, dpi=dpi, bbox_inches='tight')
  print "Saved as", savename, "\n"
  
  if raw_input("Quit[N/y]:").lower() == "y":
    break
