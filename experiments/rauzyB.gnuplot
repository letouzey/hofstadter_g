set grid
set size ratio -1
#set xrange [-1.5:1.5]
#set yrange [-1.5:1.5]
set xrange [-2:2]
set yrange [-2:2]

set linetype 1 lc rgb "dark-violet" lw 2 pt 1
set linetype 2 lc rgb "sea-green"   lw 2 pt 1
set linetype 3 lc rgb "cyan"        lw 2 pt 1
set linetype 4 lc rgb "dark-red"    lw 2 pt 1
set linetype 5 lc rgb "blue"        lw 2 pt 1
set linetype 6 lc rgb "dark-orange" lw 2 pt 1
set linetype 7 lc rgb "black"       lw 2 pt 1
set linetype 8 lc rgb "goldenrod"   lw 2 pt 1
set linetype cycle 8

tau = 0.6823278038280194

plot "/tmp/rauzy", x*(-0.5282799905780667),x*1.892935598234105, \
     "/tmp/rauzyB", \
     "/tmp/rauzyB2", "/tmp/bcoins" with linespoints, "/tmp/b3coins" with linespoints
#     "/tmp/rauzyB3", \
#     "/tmp/rauzyB4", \
#     "/tmp/rauzyB5"


