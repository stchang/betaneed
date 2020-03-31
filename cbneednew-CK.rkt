#lang racket
(require redex)
(require (only-in "cbneednew.rkt" λneed))

(provide λneed-ck red-ck φ φK subst)


(define-extended-language λneed-ck λneed
  (B hole (λ x B) (B c) (c B))
  (L hole (lab x L))
  (c x (λ x c) (c c) (lab x c)) ; lazystep terms
  (C mt (arg c) (lam x) (body x (C ...) (C ...))) ; lazystep frames
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
  ; using C so I can use it in cbneednew-redexcheck-CK-lazystep.rkt
  φK : (C ...) -> B ; should this be E?
  [(φK (C ...)) (φK_ (C ...) hole)])
(define-metafunction λneed-ck
  φK_ : (C ...) B -> B
  [(φK_ () B)   B] ; cbneednew-redexcheck-CK-lazystep.rkt needs this case
  [(φK_ (mt) B) B]
  [(φK_ ((lam x) C ...) B)   (φK_ (C ...) (λ x B))]
  [(φK_ ((arg c) C ...) B)   (φK_ (C ...) (B c))]
  [(φK_ ((body x (C_1 ...) (C_2 ...)) C ...) B)
   (φK_ (C ...) ((in-hole (φK (C_2 ...)) (λ x (in-hole (φK (C_1 ...)) x))) B))])
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
        (where (in-hole A- E_1) (φK (F_1 ...)))
        (where (in-hole E_2 A+) (φK (F_3 ...)))
        #;(side-condition (redex-match λneed (in-hole A- E) (term (φK (F_1 ...)))))
        #;(side-condition (redex-match λneed (in-hole E A+) (term (φK (F_3 ...)))))
        (side-condition (redex-match λneed A (term (φK (F_2 ...)))))
        (side-condition (redex-match λneed A (term (in-hole A+ A-))))
        var-lookup)
   ; F_4 ... can still capture stuff in v
   ; example: 
   ; ((λ r ((λ U ((λ p ((λ x (((λ r x) (p U)) (λ W (λ S r)))) 
   ;  (λ x_1 x_1))) (λ x_2 x_2))) (λ x_3 x_3))) (λ x_4 x_4))
   (--> (v (F_1 ... (body x (F_3 ...) (F_4 ...)) F_2 ...))
        (v
         (,@(term (subst-Fs (F_3 ...) x v)) F_1 ... F_4 ... F_2 ...))
        (side-condition (redex-match λneed A (term (φK (F_1 ...)))))
        βneed)))
                                   


(define-metafunction λneed-ck
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