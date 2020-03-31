#lang racket
(require redex)
(require (only-in "cbneednew.rkt" λneed))

(provide λneed-ck red-ck φ)


(define-extended-language λneed-ck λneed
  (B hole (λ x B) (B e) (e B))
  (F mt (arg e) (lam x) (body x (F ...) (F ...)))
  )

(define-metafunction λneed-ck
  balance : (F ...) -> integer
  [(balance (F_1 ... (body x (F_3 ...) (F_4 ...)) F_2 ...))
   (balance (F_1 ...))]
  [(balance (F ...)) ,(- (length (filter (redex-match λneed (arg e)) (term (F ...))))
                         (length (filter (redex-match λneed (lam x)) (term (F ...)))))])

(define-metafunction λneed-ck
  get-lam-x_ : (lam x) -> x
  [(get-lam-x_ (lam x)) x])
(define (get-lam-x t)
  (term (get-lam-x_ ,t)))

(define-metafunction λneed-ck
  bound-vars-F : (F ...) -> (x ...)
  [(bound-vars-F (F ...))  ,(map get-lam-x
                                 (filter (redex-match λneed (lam x)) (term (F ...))))])
(define-metafunction λneed-ck
  φK : (F ...) -> B ; should this be E?
  [(φK (F ...)) (φK_ (F ...) hole)])
(define-metafunction λneed-ck
  φK_ : (F ...) B -> B
  [(φK_ () B)   B] ; shouldnt get here
  [(φK_ (mt) B) B]
  [(φK_ ((lam x) F ...) B)   (φK_ (F ...) (λ x B))]
  [(φK_ ((arg e) F ...) B)   (φK_ (F ...) (B e))]
  [(φK_ ((body x (F_1 ...) (F_2 ...)) F ...) B)
   (φK_ (F ...) ((in-hole (φK (F_2 ...)) (λ x (in-hole (φK (F_1 ...)) x))) B))])
(define-metafunction λneed-ck
  φ : (e (F ...)) -> e
  [(φ (e (F ...))) (in-hole (φK (F ...)) e)])

(define red-ck 
  (reduction-relation 
   λneed-ck
   (--> ((e_1 e_2) (F ...))
        (e_1 ((arg e_2) F ...))
        push-arg)
   (-->  ((λ x e) (F ...))
         (e ((lam x) F ...))
         (side-condition (> (term (balance (F ...))) 0))
         push-lam)
   (--> (x (F_1 ... (lam x) F_2 ... (arg e) F_3 ...))
        (e ((body x (F_1 ...) (F_2 ...)) F_3 ...))
        (side-condition (not (member (term x) (term (bound-vars-F (F_1 ...))))))
        (side-condition (redex-match λneed (in-hole A- E) (term (φK (F_1 ...)))))
        (side-condition (redex-match λneed A              (term (φK (F_2 ...)))))
        (side-condition (redex-match λneed (in-hole E A+) (term (φK (F_3 ...)))))
        var-lookup)
   (--> (v (F_1 ... (body x (F_3 ...) (F_4 ...)) F_2 ...))
        (v
         (F_3 ... (lam x) (arg v) F_1 ... F_4 ... F_2 ...))
        (side-condition (redex-match λneed A (term (φK (F_1 ...)))))
        deref)))
                                   


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