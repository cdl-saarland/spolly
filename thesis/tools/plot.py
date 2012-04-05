#!/usr/bin/env python2
import numpy as np
import matplotlib.pyplot as plt

#################
###  Matmul   ###   
#################

N = 4
i5 = (20, 35, 30, 35)
i5Std =   (2, 3, 4, 2)

ind = np.arange(N)  # the x locations for the groups
width = 0.35        # the width of the bars

fig = plt.figure()
ax = fig.add_subplot(111)
rects1 = ax.bar(ind, i5, width, color='r', yerr=i5Std)

 = (25, 32, 34, 20)
 =   (3, 5, 2, 3)
rects2 = ax.bar(ind+width, , width, color='y', yerr=Std)

# add some
ax.set_ylabel('execution time (seconds)')
ax.set_title('Matrix multiplication floating point 1536x1536 values (32bit) ')
ax.set_xticks(ind+width)
ax.set_xticklabels( ('GCC -O3', 'clang -O3', 'polly ignore aliases', 'spolly') )

ax.legend( (rects1[0], rects2[0]), ('Intel(R) Core(TM) i5 CPU M 560 @ 2.67GHz (2Cores 4Threads)',
                                    'Dual-Core AMD Opteron(tm) Processor 8218 (16Cores') )

def autolabel(rects):
    # attach some text labels
    for rect in rects:
        height = rect.get_height()
        ax.text(rect.get_x()+rect.get_width()/2., 1.05*height, '%d'%int(height),
                ha='center', va='bottom')

autolabel(rects1)
autolabel(rects2)

plt.show()


