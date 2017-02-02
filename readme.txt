


Pour lancer le projet IL EST IMPORTANT de mettre l'option du nom de domaine A LA FIN de toutes les autres options
exempl : "./analyserbyte -delay 5 -singlearray -reduit"

Les options sont gérées comme suit:
Pour les boucles:
-delay n :n est un entier, pour l'accélération retardée
-unroll n : n est un entier, pour le déroulement des boucles

pour l'extension:
sans précision d'option on lance une extension classique avec un analyse de
chaque case du tableau indépendemment

-singleearray : pour lancer l'extension avec l'analyse du tableau comme une seul case

pour les domaines:
-concrete : domaine concret
-interval : domaine des intervalles
-constant : domaine des constantes
-parity : domaine des parites
-reduit : produit reduit entre le domaine des intervalles et le domaine des parites

Comme indiqué ci-dessus nous avons implémenté plusieurs domaines et différentes façon d'analyser les boucles.
Concernant les boucles nous n'avons pas implémenté les itérations décroissantes.
Nous avons choisi d'implémenter l'extension des tableaux qui est fonctionnelle aux tests avec une analyse locale de chaque variable du tableau ou une analyse globale "*" avec une seule case.

Dans l'interprète on a modifié le traitement des boucles, quand on a un retardement d'élargissement. Les n premiers tours sont réalisés avec des join et puis on passe à l'élargissement(widen). Dans le cas du déroulement de la boucle, on déroule les n premières boucles puis on passe à l'élargissement. Le widen a été implémanté dans le domaine des intervalles, dans le reste des domaines on fait simplement un join.




On a ajouté un module de produit reduit qui est composé d'une paire d'élément, un élément appartenant au domaine des intervale et l'autre au domaine des parités. De plus, on a implémenter une fonction reduce qui permet de faire le raffinement entre les deux composantes.

Pour l'extension on a modifié la parser et le lexer, le lexer en y ajoutant le traitement des crochets, dans le parser on a ajouté la
lecture de tableau dans les expressions entières et l'écriture des tableaux. En conséquence on a aussi modifié l'arbre syntaxique en y ajoutant
la lecture d'un élément du tableau.

Selon le type d'extension on rajoute à l'environnement le nom du tableau avec sa taille et (tous les index ou l'index * selon l'extension). Ce qui nous permettra de faire l'analyse abstraite et nous assurer qu'on ne sort pas du tableau. On rajoute $ devant le nom du tableau et ses variables dans l'environnment pour éviter qu'elle soit modifiées par l'utilisateur.

Lorsqu'on cherche à écrire dans une case du tableau si l'expression correspond à un seul index(on concrétise l'intervalle) ex: tab[2]=exp; on pourra modifier la valeur de l'index 2 dans l'environnement. Cependant dès que l'on a plus d'une valeur possible. Etant donné que l'on ne sait pas laquelle va être modifiée, on se contente de faire un join sur tous les index possible ex: tab[rand(1,2)]=exp -> tab[1] = join tab[1] exp, tab[2] = join tab[2] exp.

Que ce soit pour une lecture ou une écriture, on vérifie avant tout que l'intervalle d'index possible ne sort pas du tableau. Si il y a des valeurs qui sortent on envoie un warning à l'utilisateur et on filtre les mauvaises valeur. Si il n'a a aucune valeur qui est bonne on renvoie une erreur et on arrete le programme.



Par manque de temps, nous n'avons pas étendu le print pour lire un tableau (ex:print(tab[2])) -> renverra une erreur de parsing.



