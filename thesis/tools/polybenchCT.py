#!/usr/bin/env python2
import numpy as np
import matplotlib.pyplot as plt

#################
###  Matmul   ###   
#################

filename = "../latex/Figures/polybenchCT.pdf"
programs =['2mm', '3mm', 'adi', 'atax', 'bicg', 'cholesky', 'correlation', 'covariance', 'doitgen', 'dynprog', 'fdtd-2d', 'fdtd-apml', 'floyd-warshall', 'gemver', 'gemm', 'gesummv', 'gramschmidt', 'jacobi-1d-imper', 'jacobi-2d-imper', 'lu', 'ludcmp', 'mvt', 'reg_detect', 'seidel-2d', 'symm', 'syr2k', 'syrk', 'trisolv', 'trmm']  

N = len(programs)

bars  = 3
gap   = 3
width = 1        # the width of the bars
ind = np.arange(0, N * (bars + gap) * width, (bars+gap)*width)  # the x locations for the groups
ind = ind + gap * width

fig = plt.figure()
ax = fig.add_subplot(111)
ax.grid(color='gray', axis='y', linestyle='dotted', linewidth=0.3)


spolly = [2, 3, 6, 1, 2, 1, 2, 2, 1, 1, 3, 5, 0, 5, 1, 2, 1, 1, 1, 0, 2, 3, 2, 0, 2, 2, 1, 2, 2] 
rectsS = ax.bar(ind, spolly, width, color='#FFFF00')

spollydis = [1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 
rectsSd = ax.bar(ind + width, spollydis, width, color='#FF0000')

polly  = [4, 4, 0, 3, 2, 0, 1, 1, 2, 1, 1, 0, 1, 0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 2, 3, 0, 0]
rectsP = ax.bar(ind + width * 2.0, polly, width, color='#00FF00')


# add some
ax.set_axisbelow(True)
ax.set_ylabel('Number of SCoPs\n')
#ax.set_title('SPEC2000 benchmarks, compile time evaluation')
ax.set_xticks(ind + (width * 1.5))
ax.set_xlim(0, N * (gap + bars) * width + gap)
ax.set_yticks(np.arange(0, 8, 1))
ax.set_xticklabels(programs, rotation=-45, ha='left')

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
