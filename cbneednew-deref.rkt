#lang racket
(require redex)

(provide λneed red 
         valid-E? valid-D? valid-C?
         apply-red-no-dups apply-red-no-dups* apply-red-no-ambig*
         rename-bound-vars bound-vars)

(define DEBUG #f)

(define-language λneed
  (e x (λ x e) (e e))
  (x (variable-except e λ v a A n hole any C B E))
  (v (λ x e))
  (a (in-hole A v))
  (n integer)
  (C hole (λ x C) (C e))
  ; what I really want instead of C
  ; (A+ hole (A+ e) ((in-hole A A+) e))    ; C and valid-D? is equivalent to this
  ; (A- hole (λ x A-) (in-hole A (λ x A-))); C and valid-C? is equivalent to this
  #;(B (side-condition C_1 (term (balanced C_1 0 0)))) ; = A
  (A hole (in-hole (A e) (λ x A))) ; via Casey
  (E hole (E e) (λ x E)
     (side-condition 
      (in-hole C_1 ((in-hole A_1 (λ x_1 (in-hole C_2 (in-hole E_1 x_1)))) E))
      (and (redex-match λneed A (term (in-hole C_1 C_2)))
           (not (member (term x_1) (term (bound-vars-C C_2))))
           (not (member (term x_1) (term (bound-vars-E E_1))))
           (term (valid-E? E_1))
           (term (valid-D? C_1))
           (term (valid-C? C_2)))))
  )

(define-metafunction λneed
;  balance : C -> n or #f
  [(balance C) (balance_ C 0 0)])
(define-metafunction λneed
;  balance_ : C n n -> n or #f
  [(balance_ hole n_1 n_2)    ,(- (term n_2) (term n_1))]
  [(balance_ (C e) n_1 n_2)    (balance_ C n_1 ,(add1 (term n_2)))]
  [(balance_ (λ x C) n_1 n_2) ,(if (< (term n_1) (term n_2))
                                   (term (balance_ C ,(add1 (term n_1)) n_2))
                                   #f)])

(define-metafunction λneed
;  valid-E? E : -> boolean
  [(valid-E? E) (valid-E_ E 0 0)])
(define-metafunction λneed
;  valid-E_ : E n n -> boolean
  [(valid-E_ hole n_1 n_2)    ,(<= (term n_1) (term n_2))]
  [(valid-E_
    (in-hole C_1 ((in-hole A_1 (λ x_1 (in-hole C_2 (in-hole E_1 x_1)))) E))
    n_1 n_2)
   (valid-E? E)
   (side-condition
     (and (redex-match λneed A (term (in-hole C_1 C_2)))
          (not (member (term x_1) (term (bound-vars-C C_2))))
          (not (member (term x_1) (term (bound-vars-E E_1))))
          (term (valid-E? E_1))
          (term (valid-D? C_1))
          (term (valid-C? C_2))))]
  [(valid-E_ (E e) n_1 n_2)    (valid-E_ E n_1 ,(add1 (term n_2)))]
  [(valid-E_ (λ x E) n_1 n_2) ,(if (< (term n_1) (term n_2))
                                   (term (valid-E_ E ,(add1 (term n_1)) n_2))
                                   #f)]
  [(valid-E_ any n_1 n_2) #f]
  )
(define-metafunction λneed
  ; valid-D? : C -> bool
  [(valid-D? hole) #t]
  [(valid-D? ((in-hole A C) e)) 
   (valid-D? C)
   (side-condition (not (redex-match λneed hole (term A))))]
  [(valid-D? (C e)) (valid-D? C)]
  [(valid-D? any) #f])
(define-metafunction λneed
  ; valid-C? : C -> bool
  [(valid-C? hole) #t]
  [(valid-C? (λ x C)) (valid-C? C)]
  [(valid-C? (in-hole A (λ x C))) 
   (valid-C? C)
   (side-condition (not (redex-match λneed hole (term A))))]
  [(valid-C? any) #f])
  


;; subst-var: substitute variables
;;   copied from redex book page 223
(define-metafunction λneed
  [(subst-var (any_1 ...) x_1 x_2)
   ((subst-var any_1 x_1 x_2) ...)]
  [(subst-var x_1 x_1 x_2) x_2]
  [(subst-var any_1 x_1 x_2) any_1])

(define-metafunction λneed
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

;; rename-bound-vars:
;;   rename all bound variables in a given λ abstraction
;;   the second argument is the list of existing bound variables
;;
(define-metafunction λneed
  rename-bound-vars : e (x ...) -> e
  [(rename-bound-vars (λ x_1 e) (x ...))
   (λ x_new (rename-bound-vars (subst e x_1 x_new) (x_new x ...)))
   (where x_new ,(variable-not-in (term (x ... x_1))
                                  (term x_1)))
   #;(side-condition (when DEBUG
                     (printf "renaming ~a to ~a\n" (term x_1) (term x_new))))]
  [(rename-bound-vars (e_1 e_2) (x ...))
   ((rename-bound-vars e_1 (x ...)) (rename-bound-vars e_2 (x ...)))]
  [(rename-bound-vars x_1 (x ...))
   x_1])

;; bound-vars
;;  compute the set/list of bound variables in a given term
(define-metafunction λneed
  [(bound-vars (λ x e))
   (x ,@(term (bound-vars e)))]
  [(bound-vars (e_1 e_2))
   (,@(term (bound-vars e_1)) ,@(term (bound-vars e_2)))]
  [(bound-vars x)
   ()])
(define-metafunction λneed
  bound-vars-C : C -> (x ...)
  [(bound-vars-C (λ x C))
   (x ,@(term (bound-vars-C C)))]
  [(bound-vars-C (C e)) (bound-vars-C C)]
  [(bound-vars-C hole)  ()])
(define-metafunction λneed
  bound-vars-E : E -> (x ...)
  [(bound-vars-E (λ x E))
   (x ,@(term (bound-vars-E E)))]
  [(bound-vars-E 
    (in-hole C_1 ((in-hole A_1 (λ x_1 (in-hole C_2 (in-hole E_1 x_1)))) E)))
    (bound-vars-E E)
    (side-condition
     (and (redex-match λneed A (term (in-hole C_1 C_2)))
          (not (member (term x_1) (term (bound-vars-C C_2))))
          (not (member (term x_1) (term (bound-vars-E E_1))))
          (term (valid-E? E_1))
          (term (valid-D? C_1))
          (term (valid-C? C_2))))]
  [(bound-vars-E (E e)) (bound-vars-E E)]
  [(bound-vars-E hole)  ()])

(define red
  (reduction-relation 
   λneed
   (--> 
    e_lhs e_rhs
    (where 
     (in-hole
      E
      (in-hole 
       C_1 
       ((in-hole A_1 (λ x_1 (in-hole C_2 (in-hole E_1 x_1))))
        a)))
     e_lhs)
    (where ((in-hole A_2 (λ x_2 (in-hole C_3 (in-hole E_2 x_2))))
            (in-hole A_3 v_1))
           (rename-bound-vars
            ((in-hole A_1 (λ x_1 (in-hole C_2 (in-hole E_1 x_1)))) a)
            (bound-vars e_lhs)))
    (where
     e_rhs
     #;(in-hole
      E
      (in-hole 
       C_1
       (in-hole 
        A_2
        (in-hole 
         A_3
         (subst
          (in-hole C_3 (in-hole E_2 x_2))
          x_2 v_1)))))
     (in-hole
      E
      (in-hole 
       C_1
       (in-hole 
        A_2
        (in-hole 
         A_3 
         ((λ x_2 (in-hole C_3 (in-hole E_2 v_1))) v_1)
         )))))
    (side-condition (and (redex-match λneed A (term (in-hole C_1 C_2)))
                         (redex-match λneed A (term (in-hole C_1 C_3)))))
    (side-condition (and (not (member (term x_1) (term (bound-vars-C C_2))))
                         (not (member (term x_1) (term (bound-vars-E E_1))))
                         (not (member (term x_2) (term (bound-vars-C C_3))))
                         (not (member (term x_2) (term (bound-vars-E E_2))))))
    (side-condition (and (term (valid-E? E))
                         (term (valid-E? E_1))
                         (term (valid-E? E_2))))
    (side-condition (and (term (valid-D? C_1))
                         (term (valid-C? C_2))
                         (term (valid-C? C_3))))
    deref)
   ))

(define-syntax (go stx)
  (syntax-case stx ()
    [(_ t) #'(traces red (term t))]))
(define-syntax (A? stx)
  (syntax-case stx ()
    [(_ t) #'(redex-match λneed a (term t))]))
(define-syntax (re stx)
  (syntax-case stx ()
    [(_ t) #'(let ([res (apply-reduction-relation* red (term t))])
               (and (= (length res) 1)
                    res))]))
(define (remove-dups lst)
  (if (null? lst)
      lst
      (if (member (car lst) (rest lst))
          (remove-dups (rest lst))
          (cons (car lst) (remove-dups (rest lst))))))
; same as apply-reduction-relation except duplicates in result are removed
(define (apply-red-no-dups red t)
  (remove-dups (apply-reduction-relation red t)))
; applies apply-red-no-dups until an answer is reached
(define (apply-red-no-dups* red t)
  (let loop ([ts (list t)])
    (map
     (λ (x)
       (let ([next (apply-red-no-dups red x)])
         (if (null? next)
             x
             (apply append (loop next)))))
     ts)))
; appl apply-reduction-relation until answer is reached, checking that no dups are
; ever generated
(define (apply-red-no-ambig* red t)
  (let ([res (apply-reduction-relation red t)])
    (if (null? res)
        t
        (if (= (length res) 1)
            (apply-red-no-ambig* red (car res))
            #f))))