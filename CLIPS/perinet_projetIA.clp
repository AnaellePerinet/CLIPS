; Auteur : Anaëlle Perinet

; La base de faits initiale :

(deffacts initialisation_projet_IA
    ;_______________________(laby nx ny)_______________________

    ; J'ai choisi de considérer directement des valeurs entières 
    ; pour les noms de lieu/noeud et non lettre + numero car pour
    ; le "random" il faut utiliser la fonction "str-cat" pour 
    ; concaténer les deux (lettre + chiffre).
    ; Cependant cela va être sous format d'un string donc cela 
    ; complique les choses pour les conditions.

    (laby 1 2)
    
    (laby 2 7)
    (laby 2 3)

    (laby 3 2)
    (laby 3 4)
    (laby 3 5)
    (laby 3 9)

    (laby 4 5)
    (laby 4 3)
    (laby 4 7)
    (laby 4 8)

    (laby 5 3)
    (laby 5 4)

    (laby 6 9)

    (laby 7 4)
    (laby 7 2)
    (laby 7 8)

    (laby 8 7)
    (laby 8 4)

    (laby 9 3)
    (laby 9 6)

    ;__________________(tresor noeud montant)__________________
    ; On peut aussi positionner les trésors, potions, clés et portes
    ; de manière aléatoire. Cependant j'ai préfèré les placer
    ; pour m'y retrouver lors de mes tests.

    (tresor 4 300)
    (tresor 6 500)

    ;_________________(monstre nom noeud force)________________

    (monstre Patrick (random 4 7) (random 1 10))
    (monstre Bellick (random 4 7) (random 1 10))

    ;______________(epreuve noeud agilité_requise)_____________

    (epreuve 8 5)

    ;___________(potion noeud agilité_suplémentaire)___________

    (potion 3 4)

    ;___________(cle noeud nom)___________

    (cle 8 cle_1)

    ;___________(porte noeud clé)___________

    (porte 9 cle_1)
)

; Initialisation de la base des faits avec l'aventurier, le score à 0
; et la mémoire ainsi que la stratégie en mode "random/aléatoire", 
; pour sélectionner les faits de manière aléatoire.

(defrule init
	(initial-fact)
=>
	(assert (aventurier 1 6 3)) ;(aventurier noeud_actuel force agilité)
    (assert (score 0))
    (assert (memoire 1))
    (set-strategy random)
)

;------------------------------------------------------------------------

; On choisit la direction suivante où l'on souhaite aller c'est-a-dire,
; au noeud suivant.

(defrule choix_direction
    (declare (salience 5))
    (aventurier ?n ? ?)
    (laby ?n ?ny)
    (not (noeud_suiv))
    (not(fin))
=>
    (assert (noeud_suiv ?ny))
)

;------------------------------------------------------------------------

; Si le noeud suivant choisit n'est pas un noeud dit "mémoire", 
; c'est-à-dire, le même noeud que le précèdent et bien on peut
; aller au prochain et avancer dans le labyrinthe. Cela évite donc
; les aller-retour inutiles. De plus, on affiche la position de 
; l'aventurier.

(defrule nouvelle_direction
    (declare (salience 6))
    ?a <- (aventurier ?n ?f ?ag)
    ?me <- (memoire ?)
    ?n_suiv <- (noeud_suiv ?ns)
    (not(fin))
=>
    (retract ?a ?me ?n_suiv)
    (assert (aventurier ?ns ?f ?ag))
    (assert (memoire ?n))
    (printout t crlf)
    (printout t "|N" ?ns "| ")   
)

;------------------------------------------------------------------------

; Si le noeud suivant choisit est un noeud dit "mémoire", c'est-à-dire,
; le même noeud que le précèdent et bien alors on enlève la proposition 
; choisie et on réexécute donc le programme "choix_direction" jusqu'à
; qu'il choisisse un noeud non mémoire.

(defrule memoire
    (declare (salience 7))
    (aventurier ?n ? ?)
    ?me <- (memoire ?memoire_x)
    ?n_suiv <- (noeud_suiv ?ns)
    (test(eq ?memoire_x ?ns))
    (not(fin))
=>
    (retract ?n_suiv)
)

;------------------------------------------------------------------------

;(defrule mauvaise_reponse
;    ?r <- (reponse ?reponse)
;    ?a <- (aventurier ?n ? ?)
;    (not(laby ?n ?reponse))
;=>  
;    (retract ?r)
;    (printout t crlf)
;    (printout t "L'endroit ou tu veux aller n'est pas accessible." crlf)
;    (printout t crlf)
;)

;------------------------------------------------------------------------

; On vérifie si le noeud sur lequel se trouve l'aventurier ne contient
; pas un trésor, si oui c'est le cas on l'avertit, récupère la somme du 
; trésor et met à jour son score.

(defrule tresor_trouve
    (declare (salience 10))
    (aventurier ?n ? ?)
    ?t <- (tresor ?n ?m)
    ?s <- (score ?pts)
    (not(fin))
=>
    (bind ?newscore (+ ?pts ?m))
    (retract ?t ?s)
    (printout t "*TRESOR* +" ?m " pieces")
    (assert (score ?newscore))
)

;------------------------------------------------------------------------

; On vérifie si le noeud sur lequel se trouve l'aventurier ne contient
; pas un monstre de niveau inférieur ou égal à lui en comparant la force de 
; l'aventurier à celle du monstre. 
; Si c'est le cas on l'avertit de sa victoire, et l'aventurier
; peut continuer à avancer.

(defrule monstre_inf
    (declare (salience 12))
    (aventurier ?n ?f ?)
    ?m <- (monstre ?nom ?n ?fm)
    (test(<= ?fm ?f))
=>
    (retract ?m)
    (printout t "*MONSTRE* |" ?nom "||Force : " ?fm  "| Il est plus faible que toi, tu gagnes !")
)

;------------------------------------------------------------------------

; On vérifie si le noeud sur lequel se trouve l'aventurier ne contient
; pas un monstre de niveau supérieur à lui en comparant la force de  
; l'aventurier et celle du monstre. 
; Si c'est le cas on l'avertit de sa défaite, l'aventurier perd la partie,
; son score est remis à 0, et cela lui fait quitter le jeu.

(defrule monstre_sup
    (declare (salience 12))
    (aventurier ?n ?f ?)
    ?m <- (monstre ?nom ?n ?fm)
    (test(> ?fm ?f))
    ?s <- (score ?)
    (not(fin))
=>
    (retract ?s)
    (printout t "*MONSTRE* |" ?nom "||Force : " ?fm  "| Il est plus fort que toi, tu as perdu !")
    (assert (score 0))
    (assert (fin))
)

;------------------------------------------------------------------------

; Même chose pour les épreuves qu'avec les monstres.
; On vérifie si le noeud sur lequel se trouve l'aventurier ne contient
; pas une épreuve trop "dure" pour lui en comparant l'agilité de 
; l'aventurier et l'agilité nécessaire pour passer cette épreuve. 
; Si c'est le cas on l'avertit de sa défaite, l'aventurier perd la partie,
; et cela lui fait quitter le jeu.

(defrule epreuve_perdu
    (declare (salience 12))
    (aventurier ?n ?f ?ag)
    ?e <- (epreuve ?n ?e_ag)
    (test(> ?e_ag ?ag))
    (not(fin))
=>
    (printout t "*EPREUVE D'AGILITE* de niveau " ?e_ag  ", tu es trop faible en agilite (" ?ag "), tu as perdu !")
    (assert (fin))
)

;------------------------------------------------------------------------

; On vérifie si le noeud sur lequel se trouve l'aventurier ne contient
; pas une épreuve trop "facile" pour lui en comparant l'agilité de 
; l'aventurier et l'agilité nécessaire pour passer cette épreuve. 
; Si c'est le cas on l'avertit de sa victoire, et l'aventurier
; peut continuer à avancer.

(defrule epreuve_gagne
    (declare (salience 12))
    (aventurier ?n ?f ?ag)
    ?e <- (epreuve ?n ?e_ag)
    (test(<= ?e_ag ?ag))
=>
    (printout t "*EPREUVE D'AGILITE* de niveau; " ?e_ag  " tu es assez agile (" ?ag "), tu reussi ! ")
)

;------------------------------------------------------------------------

; On vérifie si le noeud sur lequel se trouve l'aventurier ne contient
; pas une potion pour lui en comparant les noeuds.
; Si c'est le cas on l'avertit qu'il a récupèré une potion et actualise 
; son agilité, on modifie donc son agilité.

(defrule potion
    (declare (salience 10))
    ?a <- (aventurier ?n ?f ?ag)
    ?p <- (potion ?n ?pt_ag)
=>
    (retract ?a ?p)
    (bind ?new_agilite (+ ?pt_ag ?ag))
    (printout t "*POTION*, tu recuperes " ?pt_ag " points d'agilite. Tu as " ?new_agilite " d'agilite maintenant. ")
    (assert (aventurier ?n ?f ?new_agilite))
)

;------------------------------------------------------------------------

; On vérifie si le noeud sur lequel se trouve l'aventurier ne contient
; pas une clé pour lui en comparant les noeuds.
; Si c'est le cas on l'avertit qu'il a récupèré une clé et on enlève la
; clé de la base des faits.

(defrule cle
    (declare (salience 10))
    ?a <- (aventurier ?n ?f ?ag)
    ?c <- (cle ?n ?ncle)
    (not (fin))
=>
    (retract ?c)
    (printout t "*CLE*, tu possedes maintenant la " ?ncle)
)

;------------------------------------------------------------------------

; On vérifie si le noeud sur lequel se trouve l'aventurier ne contient
; pas une porte verrouillé pour lui en comparant les noeuds.
; Si c'est le cas on l'avertit qu'il fait face a une porte verrouillée 
; et qu'il ne possède pas la clé pour déverouiller cette porte. Alors,
; grâce au fait "mémoire" on lui fait faire marche arrière, en le
; positionnant, au noeud précèdant.

(defrule porte_cle_non
    (declare (salience 12))
    ?a <- (aventurier ?n ?f ?ag)
    (porte ?n ?ncle)
    (cle ? ?ncle)
    ?m <- (memoire ?nme)
=>
    (retract ?a ?m)
    (assert (aventurier ?nme ?f ?ag))
    (assert (memoire ?n))
    (printout t "*PORTE VERROUILLE*, " ?ncle " non possede ..." crlf)
    (printout t "|N" ?nme "| ")
)

;------------------------------------------------------------------------

; On vérifie si le noeud sur lequel se trouve l'aventurier ne contient
; pas une porte verrouillée pour lui en comparant les noeuds.
; Si c'est le cas on l'avertit qu'il fait face a une porte verrouillée 
; et qu'il ne possède pas la clé pour déverouiller cette porte. Alors,
; grâce au fait "mémoire" on lui fait faire marche arrière, en le
; positionnant, au noeud précèdant.

(defrule porte_cle_oui
    (declare (salience 12))
    (aventurier ?n ?f ?ag)
    ?p <- (porte ?n ?ncle)
    (not(cle ? ?ncle))
=>
    (retract ?p)
    (printout t "*PORTE DEVERROUILLE*, " ?ncle " possede ! " crlf)
)

;------------------------------------------------------------------------

; Si le score de l'aventurier a atteint le maximum, ici, 800, alors on
; quitte le jeu.

(defrule score_max
    (declare (salience 15))
    (score 800)
=>
    (assert (fin))
)

;------------------------------------------------------------------------

; On affiche le score du joueur, et ainsi cela quitte le jeu. 

(defrule quitter
    (declare (salience 20))
    ?f <- (fin)
    (score ?s)
=>
    (printout t crlf)
    (printout t crlf)
    (printout t "|SCORE : " ?s "|"crlf)
    (printout t crlf)
)