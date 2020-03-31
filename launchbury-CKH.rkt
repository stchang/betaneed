#lang racket
(require redex)
(require (only-in "cbneednew.rkt" λneed))

(provide λneed-ckh red-ckh)


(define-extended-language λneed-ckh λneed
  (B hole (λ x B) (B c) (c B))
  (L hole (lab x L))
  (c x (λ x c) (c c) (lab x c)) ; lazystep terms
  (C (arg c) (lam x) (body x (C ...) (C ...))) ; lazystep frames
  (F (arg e) (var x))
  (Γ (b ...))
  (b (x e))
  )

#;(define-metafunction λneed-ck
  balance : (F ...) -> integer
  [(balance (F_1 ... (body x (F_3 ...) (F_4 ...)) F_2 ...))
   (balance (F_1 ...))]
  [(balance (F ...)) ,(- (length (filter (redex-match λneed (arg e)) (term (F ...))))
                         (length (filter (redex-match λneed (lam x)) (term (F ...)))))])

#;(define-metafunction λneed-ck
  get-lam-x_ : (lam x) -> x
  [(get-lam-x_ (lam x)) x])
#;(define (get-lam-x t)
  (term (get-lam-x_ ,t)))

#;(define-metafunction λneed-ck
  bound-vars-F : (F ...) -> (x ...)
  [(bound-vars-F (F ...))  ,(map get-lam-x
                                 (filter (redex-match λneed (lam x)) (term (F ...))))])
#;(define-metafunction λneed-ck
  ; using C so I can use it in cbneednew-redexcheck-CK-lazystep.rkt
  φK : (C ...) -> B ; should this be E?
  [(φK (C ...)) (φK_ (C ...) hole)])
#;(define-metafunction λneed-ck
  φK_ : (C ...) B -> B
  [(φK_ () B)   B] ; cbneednew-redexcheck-CK-lazystep.rkt needs this case
  [(φK_ (mt) B) B]
  [(φK_ ((lam x) C ...) B)   (φK_ (C ...) (λ x B))]
  [(φK_ ((arg c) C ...) B)   (φK_ (C ...) (B c))]
  [(φK_ ((body x (C_1 ...) (C_2 ...)) C ...) B)
   (φK_ (C ...) ((in-hole (φK (C_2 ...)) (λ x (in-hole (φK (C_1 ...)) x))) B))])
#;(define-metafunction λneed-ck
  φ : (e (F ...)) -> e
  [(φ (e (F ...))) (in-hole (φK (F ...)) e)])

(define red-ckh 
  (reduction-relation 
   λneed-ckh
   (--> ((e_1 e_2) (F ...) Γ)
        (e_1 ((arg e_2) F ...) Γ)
        push-arg)
   (-->  ((λ x e_1) ((arg e_2) F ...) (b ...))
         ((subst e_1 x y) (F ...) ((y e_2) b ...))
         (fresh y)
         push-lam)
   (--> (x (F ...) (b_1 ... (x e) b_2 ...))
        (e ((var x) F ...) (b_1 ... b_2 ...))
        var-lookup)
   (--> (v ((var x) F ...) (b ...))
        (v (F ...) ((x v) b ...))
         update-heap)))
                                   


#;(define-metafunction λneed-ck
  subst-Fs : (F ...) x v -> (F ...)
  [(subst-Fs () x v) ()]
  [(subst-Fs ((lam x_1) F ...) x_2 v) 
             ((lam x_1) ,@(term (subst-Fs (F ...) x_2 v)))]
  [(subst-Fs ((arg e) F ...) x v) 
             ((arg (subst e x v)) ,@(term (subst-Fs (F ...) x v)))]
  [(subst-Fs ((body x_1 (F_1 ...) (F_2 ...)) F ...) x_2 v)
             ((body x_1 (subst-Fs (F_1 ...) x_2 v) (subst-Fs (F_2 ...) x_2 v))
              ,@(term (subst-Fs (F ...) x_2 v)))])

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