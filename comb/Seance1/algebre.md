---
jupytext:
  formats: md:myst
  text_representation:
    extension: .md
    format_name: myst
    format_version: 0.13
    jupytext_version: 1.15.2
kernelspec:
  display_name: SageMath 10.1
  language: sage
  name: sagemath
---

# Cours Master 1 Informatique Parcours MPRI: Combinatoire et Calcul algébrique: Séance 1: Rappels d'algèbre

$\newcommand{\NN}{\mathbb{N}}
\newcommand{\ZZ}{\mathbb{Z}}
\newcommand{\QQ}{\mathbb{Q}}
\newcommand{\RR}{\mathbb{R}}
\newcommand{\CC}{\mathbb{C}}$

## Qu'est-ce que l'algèbre?

Un principe fondateur de l'algèbre est que, pour bien comprendre un
objet donné, on va non pas l'analyser en tant qu'individu isolé, mais
étudier **comment il s'insère dans le panorama**:

1. Quelle est sa [structure algébrique](https://fr.wikipedia.org/wiki/Structure_alg%C3%A9brique),
   c'est à dire quelles sont ses opérations de base et leurs
   propriétés (axiomes)?

2. Comment se relie-t'il à d'autres objets?

Ainsi, pour 1. plutôt que de s'intéresser séparément aux nombres
réèls, aux nombres complexes, etc, on va étudier les ensembles munis
d'une addition et d'une multiplication, avec les propriétés idoines
(associativité, ...), et déterminer les théorèmes généraux qui en
découlent. Cette approche est de nature très similaire à la
programmation objet: on définit des classes abstraites (=structures
algébriques), que l'on peuple de méthodes génériques (=théorèmes)
valides dès que les spécifications (=axiomes) sont satisfaites. Il ne
restera plus qu'à implanter les opérations de base (=définir
l'addition, la multiplication), pour utiliser les méthodes génériques
sur (= appliquer les théorèmes généraux à) l'objet étudié.

Pour 2. on va étudier les *morphismes* entre les objets --
c'est-à-dire les fonctions qui préservent la structure -- et comment
ils se composent. Là on se rapproche la programmation fonctionnelle.

Une autre idée forte est que **plus il y a de la structure, plus un
objet est rigide et les algorithmes pour calculer avec sont
efficaces**.

Exemple: dictionnaires et bases de données

Tout cela pour dire que programmer et faire de l'algèbre, ce n'est pas
si éloigné que cela.

**Adage du calcul algébrique:** Diviser pour régner

## Structures algébriques communes

### Exemples

Que connaissez vous comme:

#### Ensembles munis d'opérations?

- réels $(\RR,+,*,0,1,-,/,<)$
- entiers naturels $(\NN,+,-, *,0,1, //, =, \gt, \lt)$
- entiers relatifs $(\ZZ,+,-, *, //)$ (// est la division entière)
- rationnels $\QQ$ $(\QQ, +, -, *, /)$ (/ uniquement si on ne divise pas par 0)
- complexes $(\CC,+,*,0,1,-,/)$
- vecteurs dans $\RR^3$: $(\RR^3, +, -, 0, =)$
- matrices $(M_n(\RR), +, -, *, 0, Id)$ où $0$ est la matrice nulle, * est le produit matriciel
- $E$ : l'ensemble des langages rationnels $(., +, *, \cup, \cap, \setminus)$ (tous les langages ne sont pas forcément clos par $\cup, \cap, \setminus$)

#### Opérations

- opérations ensemblistes: $\cup$, ...
- égalité: $=$, $\neq$
- addition: + et dérivées éventuelles: -, 0
- multiplication * et dérivées éventuelles: / division, élément neutre 1
- racine/exponentiation
- produit scalaire
- comparaisons: $<$ et dérivées: $\leq$,  $>$ 

#### Propriétés / axiomes

Notons $E$ l'ensemble sur lequel on met de la structure.

- loi interne / "stabilité" par l'opération : $\forall a, b \in E, \qquad a + b \in E$
- propriétés de fermeture

Propriété des opérations arithmétiques:
- élément neutre $e$: $\forall a \in E, \; a+e = e+a = a$
- existence du symétrique : $\forall a \in E, \exists b \in E, a+b = b+a = e$ (où $e$ est l'élément neutre)
- commutativité: $a + b = b + a, \qquad \forall a\in E, b\in E$
- associativité: $\forall a, b, c \in E \qquad a + (b + c) = (a + b) + c$
- distributivité de la multiplication sur l'addition: $\forall a, b, c \in E \qquad a(b+c) = ab + ac$

Propriétés des opérations de comparaisons:
- Symétrie : $\forall a, b \in E, \; a = b \qquad \longleftrightarrow \qquad b=a$
- Antisymétrie : $\forall a, b \in E, (a \leq b \wedge b \leq a) \Rightarrow a = b$
- Reflexivité : $\forall x \in E, \; x = x$
- Transitivité : $\forall a, b, c \in E, \; a = b \wedge b = c \Rightarrow a = c$ 
- $a-b \gt 0 \leftrightarrow a \gt b$
- $a \gt b \leftrightarrow b \lt a$
- (optionnel) Totalité : $\forall a, b \in E, \qquad a \leq b \lor b \leq a$

### Structures algébriques à une opération 

Commençons par le commencement. Qu'y a-t'il de commun entre les
entiers, les nombres réels, les symétries d'une figure géométrique, le
Rubicks Cube, ou une pile de T-shirts dans un placard?

Dans tous les cas il y a un **monoïde** sous-jacent. Qu'est-ce qu'un
monoïde?

:::{admonition} Définition

Un monoïde est un **ensemble** $E$, muni d'une **opération binaire
interne** $.$ **associative** avec **élément neutre** $e$.

- opération binaire: fonction $E\times E -> E$

- associative: $(a . b) . c = a . (b . c) \forall a,b

- élément neutre: $a . e = e . a = a \forall a$

:::

:::{admonition} Exemples

- $(M_n(\RR), +, 0)$
- $(\NN, +, 0)$
- $(\ZZ, +, 0)$
- $(\ZZ, -, 0)$ : non associatif: $1 - (2 - 4) \neq (1 - 2) - 4$
- $(\QQ, *, 1)$
- $(\RR, *, 1)$
- $(E,\cup, \emptyset)$ où $E$ est un ensemble d'ensemble stable par union
- $(E,\cap, U)$ où $E$ est un ensemble d'ensemble inclus dans univers $U$, avec $E$ stable par intersection
- (B l'ensemble des booléens, $\lor$, $\bot$)
- $(\mathcal{F}, \circ, id)$ où $\mathcal{F}$ est l'ensemble des fonctions et $\circ$ est la compositions de fonctions
- $(\NN, max, 0)$ Exercice: prouver que max est associatif
- $(\NN \cup \{+\infty\}, min, +\infty)$

:::

### Exemple: exponentiation rapide

Objectif: calculer rapidement $a^4=a*a*a*a$

Méthode naïve: $a^4= ((a*a)*a)*a$
Méthode rapide: $a^4= (a*a)*(a*a)$
Algo: $a = a*a; a = a*a$ 

Généralisation: $a^n$ se calcule en $log_2(n)$ opérations

### Exemple: Paradigme Map-Reduce

Objectif:
- On a un gros jeu de données $E$; tellement gros qu'il ne rentre par sur une seule machine.
- On a une opération sur ce jeu de donnée qui s'exprime suit:
    - Map: Appliquer une fonction $f$ à tous les éléments   
    - Reduce: une opération, associative, qui combine tous les résultats

- Ce qu'on veut calculer: `reduce(f(x) for x in E)`

Application bête: compter le nombre d'éléments de $E$:
- Map: f: x -> 1
- Reduce: + 

Application: faire une recherche: est-ce que e est dans $E$
- Map: f: x -> x==e ?
- Reduce: ou

Recherches plus complexes

Quel rapport avec l'associativité?

Elle permet de diviser pour régner:

Si $E$ est la concaténation de $E1$ et $E2$ alors:

`reduce( reduce(f(x) for x in E1), reduce(f(x) for x in E2) )`

Avec la commutativité  en plus, on peut couper $E$ en deux de n'importe quelle façon.

### Exemple: programmation fonctionnelle et monades

### Exemple: coloration des faces d'un cube

:::{admonition} Problème

De combien de façons différentes peut-on colorier les faces d'un cube?
:::

Passons aux symétries: vous savez maintenant depuis longtemps que,
pour résoudre efficacement un problème, il est bon d'étudier et
exploiter ses symétries: c'est à dire l'ensemble des transformations
qui ne changent pas le problème.

Lorsque l'on a deux symétries, on peut les composer; le résultat est
toujours une symétrie. La composition est associative. Ne rien faire
est une symétrie. L'ensemble des symétries muni de la composition est
donc un monoïde.

En fait, on a plus que cela: l'application d'une symétrie est une
opération réversible: on peut l'inverser.

On a un **groupe**: un monoïde où tout élément a un inverse.

On a des algorithmes qui permettent de calculer avec des très gros
groupes. De taille factorial(1000).

Pour un problème donné, on va considérer l'ensemble de ses symétries

### Exemple: Le Rubicks cube

De quel ensemble, muni de quelle opération parle-t'on dans le Rubicks
cube?

Ce qui a être intéressant, ce n'est pas tellement les configurations
possibles du Rubicks cube, mais les transformations que l'on peut
effectuer: faire tourner une face, faire tourner le cube, et surtout
enchaîner ses transformations. Ce que l'on étudiera, c'est l'ensemble
de toutes les transformations que l'on peut obtenir par composition de
transformations élémentaires; l'opération est la
composition. L'élément neutre, c'est ne rien faire.

Là encore, c'est un groupe.

### Exemple: Gestion de piles de T-Shirts

Opérations élémentaires: prendre le i-ème T-Shirt
et le poser tout en haut (pas inversible!)

Monoïde de toutes les opérations obtenues par composition.

Il a de bonnes propriétés liés à un ordre. Il est dit R-trivial => théorèmes et algorithmes pour analyser l'évolution du système. Avec de la jolie combinatoire.

### Semi-Anneaux, Anneaux, Corps


TODO: expliciter la construction des ensembles usuels par relations
d'équivalence / quotient: le plus petit ensemble qui ... on veut telle
propriété; on procède comme ça ...

$(\NN, +,*)$: associativité de + et *, commutativité de + et *, distributivité de + sur *, 0 élément neutre de +, 1 élément neutre de *.

C'est un **semi-anneau**.

$(\ZZ, +,*)$: comme pour $\NN$, mais avec opposés (inverse pour la soustraction)

C'est un **anneau**.

$(\QQ, +, *)$: pourquoi on a inventé les rationnels: c'est le plus petit ensemble contenant $\ZZ$ et stable par division: existence d'inverse pour tout le monde sauf $0$.

C'est un **corps**.

$(\RR,+,*)$: **corps complet**: propriété de limites des suites de Cauchy; là on va du côté de l'analyse. Moins utile pour nous. Mais il y a d'autres corps complets très pertinent pour le calcul exact (nombres $p$-adiques). Et puis il n'y a qu'infiniment peu de nombre réèls que l'on puisse représenter sur machine.

$(\CC,+,*)$: **corps algébriquement clos**: on veut avoir les racines de n'importe quel nombre. Plus généralement: tout polynôme admet une racine. Même défaut que pour $\RR$.

Dans la pratique, on va calculer avec des corps plus petits, obtenus par extensions de $\QQ$ pour rajouter juste les éléments dont on a besoin pour notre calcul. Par exemple $\QQ[\sqrt(2)]$.

### Exemple: corps finis $GF(p)$:

Prenons $p=5$ (ou plus généralement un nombre premier). On va
construire les entiers modulo $p$ et le munir d'une structure de
corps.

On considère la relation d'équivalence $x\sim y$ si $y-x \mod p
=0$. Pour $x\in \ZZ$, on va noter $\overline x= \{y, y-x \mod p = 0\}$
la classe d'équivalence de $x$.

Exemple: $\overline{4} = \{ ... -1, 4, 9, 14, ... \}$

Soit $E=\ZZ/p\ZZ$ l'ensemble des classes d'équivalence:

$$E=\{\overline{0},\overline{1},\overline{2},\overline{3},\overline{4}\}$$

On définit les opérations + et * sur $E$ par:

$$\overline{x} + \overline{y} = \overline{x+y}$$
$$\overline{x} * \overline{y} = \overline{x*y}$$

et pareil pour les autres opérations (-, ...)
 
Miracle: le résultat ne dépends pas du choix de représentants $x$ et
$y$. Les opérations sont bien définies. De plus toutes les propriétés
de $\ZZ$ (associativé, ...) restent valides. On obtient donc un
anneau.

Exemple: (sans mettre les barres pour alléger)

| + | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| 0 | 0 | 1 | 2 | 3 | 4 |
| 1 | 1 | 2 | 3 | 4 | 0 |
| 2 | 2 | 3 | 4 | 0 | 1 |
| 3 | 3 | 4 | 0 | 1 | 2 |
| 4 | 4 | 0 | 1 | 2 | 3 |

| * | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| 0 | 0 | 0 | 0 | 0 | 0 |
| 1 | 0 | 1 | 2 | 3 | 4 |
| 2 | 0 | 2 | 4 | 1 | 3 |
| 3 | 0 | 3 | 1 | 4 | 2 |
| 4 | 0 | 4 | 3 | 2 | 1 |

| x | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
|1/x| ND| 1 | 3 | 2 | 4 |

On constate que tous les éléments, sauf $0$ admettent un inverse. Du coup, $E$ est un corps. Fini de surcroît.

Du fait qu'ils sont finis, ces corps et leurs généralisations se représentent très naturellement sur ordinateur. Il vont jouer un rôle essentiel pour les codes correcteurs, la cryptographie, ... et le calcul en général.

### Espaces vectoriels

### Exemples d'ensembles munis d'opérations dans Sage

```{code-cell} ipython3
ZZ
```

```{code-cell} ipython3
K = GF(5)
```

```{code-cell} ipython3
K
```

```{code-cell} ipython3
K(4)
```

### Algèbre générale: zoologie des maths

[Structures algébriques dans SageMath](https://github.com/OpenDreamKit/OpenDreamKit/raw/master/ReportingPeriod2/ReviewPresentations/Pictures/sage-category-graph.pdf)

## Algèbre universelle

**Adage:** traiter uniformément toutes les structures algébriques

### Sous-structures

Comment les définir?

Comment les décrire?

### Objets libres

## Algèbre linéaire

## Motivation

Considérons les vecteurs suivants:
$$(0, 0, 3, 1, 4), (3, 1, 4, 2, 1), (4, 3, 2, 1, 3)$$

On souhaite déterminer si les vecteurs suivants sont des combinaisons linéaires des précédents:

$$ u = (1,2,4,1,0) \qquad v = (2,1,4,0,1)$$

On va continuer dans Sage. Voir la feuille de travail incluse dans le devoir.

# Un peu d'algèbre linéaire à la main dans Sage

```{code-cell} ipython3
K = GF(5)
```

```{code-cell} ipython3
K.cardinality()
```

```{code-cell} ipython3
K.category().axioms()
```

```{code-cell} ipython3
%display latex
```

Définissons une matrice, vue comme collection de vecteurs lignes:

```{code-cell} ipython3
M = matrix(K, [[0,0,3,1,4], [3,1,4,2,1], [4,3,2,1,3]]); M
```

```{code-cell} ipython3
v0 = M[0]
v1 = M[1]
v2 = M[2]
```

Et prenons deux vecteurs:

```{code-cell} ipython3
u = vector(K, [1, 2, 4, 1, 0])
v = vector(K, [2, 1, 4, 0, 1])
```

**Problème:**
Est-ce que $u$ est dans le sous-espace vectoriel engendré par v0,v1,v2 ? 

Autrement dit: peut-on trouver a0,a1,a2 de sorte que:

$$ u = a0 v0 + a1 v1 + a2 v2 $$

```{code-cell} ipython3
M
```

```{code-cell} ipython3
u
```

Trouver a0,a1,a2 de sorte que:
- 1 = a0*0 + a1 *3 + a2 * 4
- ...
- ...

+++

Mettons notre matrice sous **forme échelon**

```{code-cell} ipython3
M
```

```{code-cell} ipython3
M[0], M[1] = M[1], M[0]
```

```{code-cell} ipython3
M
```

```{code-cell} ipython3
M[0] = M[0] / M[0,0]
```

```{code-cell} ipython3
M
```

```{code-cell} ipython3
u
```

```{code-cell} ipython3
M[2,0]
```

```{code-cell} ipython3
M[2] = M[2] - 4 * M[0]
```

```{code-cell} ipython3
M
```

```{code-cell} ipython3
u
```

a0 M[0] + a1 M[1] + a2 M[2]  =  u

Équations:
-   a0      = 1
- 2*a0      = 2
- 3*a0+3*a1 = 4

```{code-cell} ipython3
M[1] = M[1] / K(3)
```

```{code-cell} ipython3
M
```

```{code-cell} ipython3
M[0] = M[0] * K(3)
```

```{code-cell} ipython3
M
```

```{code-cell} ipython3
M[0] = M[0] - 3 * M[1]
```

```{code-cell} ipython3
M
```

```{code-cell} ipython3
u
```

a0 M[0] + a1 M[1] + a2 M[2]  =  u

Équations:
-   a0 = 1
- 2*a0 = 2
-   a1 = 4
- 3a0+2a1=1
- 3a0+3a1=0

```{code-cell} ipython3
K(3*1 + 2*4)
```

```{code-cell} ipython3
u - (1 * M[0] + 4 * M[1])
```

On dit que $M$ est sous forme échelon réduite

```{code-cell} ipython3
M
```

Notion de bonne matrice: sous forme échelon réduite
Algorithme pour obtenir une matrice sous forme échelon
à partir d'une matrice quelconque.

```{code-cell} ipython3

```

## Exemple: plans dans l'espace $\RR^3$

## Forme échelon d'une matrice


# Résumé

## SageMath

Logiciel libre de calcul mathématique basé sur Python

## Algèbre

**Adage**: comprendre un objet en étudiant comment il s'insère dans le
panorama:

1. Quelle est sa [structure algébrique](https://fr.wikipedia.org/wiki/Structure_alg%C3%A9brique),
   c'est à dire quelles sont ses opérations de base et leurs
   propriétés (axiomes)?
2. Comment se relie-t'il à d'autres objets?

## Algèbre Générale

Zoologie des structures algébriques en maths: monoïdes, groupes,
anneaux, corps, espaces vectoriels, ...

## Algèbre Universelle

**Adage:** traiter uniformément toutes les structures algébriques

## Algèbre linéaire

## Calcul Algébrique

**Adages**:
- Diviser pour régner
- Méthodes d'élimination
- Méthodes d'évaluation et changement de représentation
