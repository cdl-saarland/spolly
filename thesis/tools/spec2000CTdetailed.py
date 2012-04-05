#!/usr/bin/env python2
import numpy as np
import matplotlib.pyplot as plt

#################
###  Matmul   ###   
#################

N = 6

filename = "../latex/Figures/SPEC2000CTsSCoPsOne.pdf"

width = 0.2        # the width of the bars
ind = np.arange(0, N*(1+width*2), 1+width*2)  # the x locations for the groups
ind = ind + width

fig = plt.figure()
ax = fig.add_subplot(111)
ax.grid(color='gray', axis='y', linestyle='dotted', linewidth=0.3)


spolly = (45, 16, 7, 23, 15, 33)
rectsOverall = ax.bar(ind, spolly, width, color='#FFFF00')

aliasesone = [15, 7, 1, 7, 8, 14]
rectsAliasesOne = ax.bar(ind + (1 * width), aliasesone, width, color="#339933")
loopsone = [0, 0, 0, 0, 0, 0]
rectsLoopsOne = ax.bar(ind + (2 * width), loopsone, width, color="#00FFFF")
conditionalsone = [0,0,0,0,0,0]
rectsConditionalsOne = ax.bar(ind + (3 * width), conditionalsone, width, color="#FF00FF")
functioncallsone = [33, 0, 4, 7, 2, 16]
rectsFunctionCallsOne = ax.bar(ind + (4 * width), functioncallsone, width, color="#FF3333")

loops = [105, 34, 15, 67, 72, 46]
#rectsLoops = ax.bar(ind + (2 * width), loops, width, color="#0000FF")
conditionals = [13, 10, 7, 66, 6, 13]
#rectsConditionals = ax.bar(ind + (4 * width), conditionals, width, color="#FF00FF" )
crucialbranches = [12, 0, 0, 6, 0, 2]
#rectsCrucialBranches = ax.bar(ind + (5 * width), crucialbranches, width, color="#FF0000" )


# add some
ax.set_axisbelow(True)
ax.set_ylabel('speculative valid SCoPs\n')
#ax.set_title('SPEC2000 benchmarks, compile time evaluation')
ax.set_xticks(ind + (width * 2))
ax.set_yticks(np.arange(0, 45+6, 5))
ax.set_xticklabels(('ammp', 'art', 'bzip2', 'crafty', 'equake', 'vpr'))

ax.legend( (rectsOverall[0], rectsAliasesOne[0], rectsLoopsOne[0], 
            rectsConditionalsOne[0], rectsFunctionCallsOne[0]),
              (
               'number of sScops', 
               'sSCoPs containing aliasing instructions',
               'sSCoPs containing loops TODO', 
               'sSCoPs containing conditionals TODO', 
               'sSCoPs containing function calls', 
              )
         )

def autolabel(rects):
    # attach some text labels
    for rect in rects:
        height = rect.get_height()
        ax.text(rect.get_x()+rect.get_width()/2. + 0.02, height + 0.2, '%d'%int(height),
                ha='center', va='bottom')

#autolabel(rectsS)
#autolabel(rectsSd)
#autolabel(rectsP)

DefaultSize = fig.get_size_inches()
fig.set_size_inches(DefaultSize[0],DefaultSize[1])

DefaultSize = fig.get_size_inches()
print "Size in Inches", DefaultSize
DPI = 100
print "Which should result in a %i x %i Image"%(DPI*DefaultSize[0], DPI*DefaultSize[1])

fig.savefig(filename, dpi=(200), bbox_inches='tight')
print "Saved as", filename
