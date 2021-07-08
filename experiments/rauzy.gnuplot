set grid
set size ratio -1
set xrange [-1.5:1.5]
set yrange [-1.5:1.5]

tau = 0.6823278038280194

set multiplot

# /tmp/rauzy : cf test_rauzy.ml

plot "/tmp/rauzy", x*(-0.5282799905780667),x*1.892935598234105, tau*1.25, -tau*1.25, (-1-x)/tau, (1-x)/tau
set polar
plot (1.067*sqrt(2)/sqrt(tau+1+(tau-1)*cos(2*t)+tau*tau*sin(2*t)))
unset polar
