## A propos d'une curieuse famille de fonctions récursives imbriquées due à Hofstadter

Au chapitre 5 du fameux livre "Gödel, Escher, Bach", D. Hofstadter
introduit la fonction G suivante comme exemple de définition récursive:

    G(0)=0 puis G(n)=n-G(G(n-1)) pour tout entier n>0

Il définit également une fonction H selon le même modèle, mais avec
trois appels récursifs imbriqués au lieu de deux pour G, et mentionne
que cela continue ensuite, pour n'importe quel degré d'imbrication.
Cet exposé est consacré à l'étude de la famille de fonctions que l'on
obtient ainsi. Je parlerai de leurs liens intimes avec (au moins!)
des arbres rationnels infinis, des variantes des nombres de Fibonacci
et leur systèmes de numération associés, des mots morphiques, des
nombres de Pisot, des fractales de Rauzy. Je présenterai également le
développement Coq correspondant, certifiant presque toutes les
propriétés en question, y compris une conjecture OEIS concernant H.
Cela m'a amené à considérer en Coq des réels, complexes, polynômes,
matrices, etc, ce qui est encore loin d'être une sinécure. Il sera
enfin question d'une conjecture personnelle récalcitrante : cette
famille de fonctions semble croissante point-à-point.

NB: Il y aura un recouvrement certain mais loin d'être total avec un
exposé précédent aux journées PPS 2018, consacré à l'époque à G et à
un exercice au lecteur posé par Hostadter à propos de "l'arbre miroir"
de G. Pas besoin ici d'avoir vu cet exposé 2018 !
