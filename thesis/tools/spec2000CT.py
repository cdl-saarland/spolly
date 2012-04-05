#!/usr/bin/env python2
import numpy as np
import matplotlib.pyplot as plt

#################
###  Matmul   ###   
#################

N = 8

filename = "../latex/Figures/SPEC2000CT.pdf"

ind = np.arange(N)  # the x locations for the groups
width = 0.2        # the width of the bars
ind = ind + width

fig = plt.figure()
ax = fig.add_subplot(111)
ax.grid(color='gray', axis='y', linestyle='dotted', linewidth=0.3)


spolly = (45, 16, 7, 23, 15, 0, 0, 33)
rectsS = ax.bar(ind, spolly, width, color='#FFFF00')

spollydis = (30, 5, 4, 9, 2, 1, 24, 26)
rectsSd = ax.bar(ind + width, spollydis, width, color='#FF0000')

polly  = (12, 5, 13, 23, 10, 6, 6, 17)
rectsP = ax.bar(ind + width * 2.0, polly, width, color='#00FF00')

maximP = max(polly)
maximS = max(spolly)
maxim  = max(maximP, maximS)

# add some
ax.set_axisbelow(True)
ax.set_ylabel('Number of SCoPs\n')
#ax.set_title('SPEC2000 benchmarks, compile time evaluation')
ax.set_xticks(ind + (width * 1.5))
ax.set_yticks(np.arange(0, maxim+6, 5))
ax.set_xticklabels(('ammp', 'art', 'bzip2', 'crafty', 'equake', 'gzip', 'twolf', 'vpr'))

ax.legend( (rectsS[0], rectsSd[0], rectsP[0]),
              ('speculative valid SCoPs (SPolly)',
               'discarded speculative valid SCoPs (SPolly)', 
               'valid SCoPs (Polly)') )

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
fig.set_size_inches(DefaultSize[0]*2,DefaultSize[1])

DefaultSize = fig.get_size_inches()
print "Size in Inches", DefaultSize
DPI = 100
print "Which should result in a %i x %i Image"%(DPI*DefaultSize[0], DPI*DefaultSize[1])

fig.savefig(filename, dpi=(200), bbox_inches='tight')
print "Saved as", filename



