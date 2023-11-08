---
jupytext:
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

# TP

## [accès aux logiciels et au matériel pédagogique](../README.md)

Pour cette séance, le devoir sera essentiellement vide. L'utilisation
du dépôt `git` sera principalement une manière pratique pour vous pour
sauvegarder et transférer votre travail, et pour nous pour le
consulter, le noter et, le cas échéant, collaborer avec vous pour vous
aider.

## Consignes

Tout code non trivial doit être dans le fichier
[moncode.py](moncode.py). S'il devient trop long, vous pouvez créer
d'autres fichiers, en les mentionnant dans le rapport.

Toute fonction doit:
- être documentée  
  la documentation doit inclure des exemples et une estimation rapide
  de la *complexité algorithmique* de la fonction;
- être testée  
  voir l'exemple fourni pour comment rédiger les tests sous forme de
  doctests;
- utiliser chaque fois que possible des
  [annotations de type](https://docs.python.org/3/library/typing.html).

Vous devez avoir vérifié votre code avec des analyseurs statiques
comme `pyflakes` ou `mypy`.

Vous devez en outre rédiger au fur et à mesure un rapport concis
mettant en valeur votre travail.

## Prise en main

Consultez le fichier [moncode.py](moncode.py) et le squelette de
rapport dans le [README.md](README.md).

### Indications

Importer les objets définis dans `moncode.py` et les recharger
automatiquement en cas de changement:

```{code-cell} ipython3
%load_ext autoreload
%autoreload 2
from moncode import *
```

Utilisation:

```{code-cell} ipython3
response("As-tu faim")
```

Consultation de la documentation:

```{code-cell} ipython3
response?
```

Vérifications statiques:

```{code-cell} ipython3
!pyflakes moncode.py
```

```{code-cell} ipython3
!mypy moncode.py
```

Lancement des tests:

```{code-cell} ipython3
!sage -t moncode.py
```

Pour utiliser des objets de Sage dans `moncode.py`, par exemple pour
des annotations de type, il faut les importer:

``` python
from sage.all import matrix, GF  # type:ignore
```

## Élimination de Gauß

Implantez l'algorithme de Gauß de mise sous-forme échelon réduite
d'une matrice à coefficients dans un corps.

``` python
    def forme_echelon_réduite(m: matrix) -> matrix:
        """
        Renvoie la matrice `m` mise sous forme échelon 
        """
```

Quelle est la complexité de votre implantation?

:::{note}

Pour chaque analyse de complexité de ce cours, vous précisez bien le
modèle de calcul (taille des problèmes, opérations élémentaires) et
vous justifierez le résultat obtenu:

:::

## Test d'appartenance à un sous espace vectoriel

Soit $V=(v_i)_i$ une liste de vecteurs. On souhaite déterminer si un
vecteur $w$ est dans le sous-espace vectoriel engendré par les
$(v_i)_i$.

Implantez une fonction:

``` python
   def appartientSEV(V, w):
       """
       Teste si `w` est engendré par les vecteurs dans `V`.
       """
```

Vous utiliserez la fonction `forme_echelon_réduite`.

Pourrait-t'on se contenter d'une matrice sous forme échelon?

Quelle est la complexité de votre implantation?

## Calcul d'une base de la somme de deux sous espaces vectoriels

Soient $U$ et $V$ deux sous espaces vectoriels d'un même espace
vectoriel $W$, décrits chacun par une base exprimée dans la base
canonique de $W$. Implanter un algorithme calculant une base de la
somme $U+V$ de ces deux sous espaces vectoriels.

Quelle est la complexité de votre implantation?
