Titre: La fonction G de Hofstadter et au-delà, un exemple curieux mêlant calculs et preuves sur ordinateur
==========================================================================================================

Dans son livre "Gödel, Escher, Bach", Douglas Hofstadter
définit une fonction récursive G ainsi:

    G(0)=0 puis G(n)=n-G(G(n-1)) pour tout entier n>0.

Cette définition se généralise ensuite, donnant une curieuse famille
de fonctions, nettement moins connues que G. Leur étude entremêle une
étonnante variété de notions : arbres infinis, variantes de nombres de
Fibonacci et systèmes de numération associés, mots morphiques, jolie
fractale, etc. Plusieurs questions restent, des conjectures résistent
encore. On verra comment le calcul est crucial ici pour se forger des
intuitions (pas toujours exactes!) et comment des preuves sur
ordinateur (ici en Coq) aident à se prémunir de tout type d'erreurs.

## Références

https://fr.wikipedia.org/wiki/Suite_de_Hofstadter
https://github.com/letouzey/hofstadter_g
