#lang racket
(require redex)

(provide lazystep lazystep-red subst)

(define-language lazystep
  (d x (λ x d) (d d))
  (e x (λ x e) (e e) (lab x e))
  (x variable-not-otherwise-mentioned)
  (L hole (lab x L))
  (v (in-hole L (λ x e)))
  (E hole (E e) (lab x E)))

(define lazystep-red
  (reduction-relation
   lazystep
   (--> (in-hole E ((in-hole L (λ x e_1)) e_2))
        (update E (subst e_1 x (lab x e_2))))))


;; subst-var: substitute variables
;;   copied from redex book page 223
(define-metafunction lazystep
  [(subst-var (any_1 ...) x_1 x_2)
   ((subst-var any_1 x_1 x_2) ...)]
  [(subst-var x_1 x_1 x_2) x_2]
  [(subst-var any_1 x_1 x_2) any_1])

(define-metafunction lazystep
  ; 1) x_1 bound, so don't continue in λ body
  [(subst (λ x_1 any_1) x_1 any_2)
   (λ x_1 any_1)]
  
  ; 2) do capture-avoiding subst by generating fresh name
  [(subst (λ x_1 any_1) x_2 any_2)
   (λ x_new
     (subst (subst-var any_1 x_1 x_new) x_2 any_2))
   (where x_new ,(variable-not-in (term (x_2 any_1 any_2))
                                  (term x_1)))
   #;(side-condition (when DEBUG
                     (printf "renaming ~a to ~a\n" (term x_1) (term x_new))))]
  ; 3) replace x_1 with any_1
  [(subst x_1 x_1 any_1) any_1]
  
  ;; the last two cases just recur on the tree structure of the term
  [(subst (any_2 ...) x_1 any_1)
   ((subst any_2 x_1 any_1) ...)]
  [(subst any_2 x_1 any_1)
   any_2])




;; ----------------------------------------------------------------------------
;; update
; updates all labels with the one that was just reduced
(define-metafunction lazystep
  update : E e -> e
  [(update E e) 
   (replace-lab-body (in-hole E e) (find-inner-lab E) (in-hole (find-inner-lab-E E) e))])
                   
; find-inner-lab : E -> x
; returns id of innermost labeled term in given context E
; (innermost lab is lowest in the syntax tree)
(define-metafunction lazystep
  find-inner-lab : E -> x
  [(find-inner-lab E) (find-inner-lab-help E x_1000)])
(define-metafunction lazystep
  find-inner-lab-help : E x -> x
  [(find-inner-lab-help hole x)          x]
  [(find-inner-lab-help (lab x_1 E) x_2) (find-inner-lab-help E x_1)]
  [(find-inner-lab-help E x)             (find-inner-lab-help (next-E E) x)])


; find-inner-lab-E : E -> E
; finds the innermost labeled term, and returns the E within that labeled term
; (innermost label is lowest in the syntax tree)
(define-metafunction lazystep
  find-inner-lab-E : E -> E
  [(find-inner-lab-E E) (find-inner-lab-E-help E E)])
(define-metafunction lazystep
  find-inner-lab-E-help : E E -> E
  [(find-inner-lab-E-help hole E)        E]
  [(find-inner-lab-E-help (lab x E_1) E) (find-inner-lab-E-help E_1 E_1)]
  [(find-inner-lab-E-help E_1 E)         (find-inner-lab-E-help (next-E E_1) E)])


; next-E : E -> E or #f
; returns #f if input E is a hole
(define-metafunction lazystep
  next-E : E -> E or #f
  [(next-E hole)     #f]
  [(next-E (E e))     E]
  [(next-E (lab x E)) E])


; replace-lab-body : e_1 x e_2 -> e
; in e_1, replace body of all labels with specified id x, with given e_2
(define-metafunction lazystep
  [(replace-lab-body x_1 x_2 e) x_1]
  [(replace-lab-body (lab x e_1) x e_2)     (lab x e_2)]
  [(replace-lab-body (lab x_1 e_1) x_2 e_2) (lab x_1 (replace-lab-body e_1 x_2 e_2))]
  [(replace-lab-body (e_1 e_2) x e_3)       ((replace-lab-body e_1 x e_3)
                                             (replace-lab-body e_2 x e_3))]
  [(replace-lab-body (λ x_1 e_1) x_2 e_2)   (λ x_1 (replace-lab-body e_1 x_2 e_2))])

; subst-holes : E* M -> M
; plug M into all holes in E*, where E* is a context that can have multiple holes
#;(define-metafunction lazystep
  [(subst-holes hole M) M]
  [(subst-holes (any ...) M) ((subst-holes any M) ...)]
  [(subst-holes any M) any])