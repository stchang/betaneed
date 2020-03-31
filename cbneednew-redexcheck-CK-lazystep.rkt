#lang racket
(require redex)
(require "cbneednew.rkt")
(require "cbneednew-CK.rkt")
(require "lazystep.rkt")

(define-metafunction λneed
  fv : e -> (x ...)
  [(fv e) (remove-duplicates (fv_ e))])
(define-metafunction λneed
  fv_ : e -> (x ...)
  [(fv_ x)    (x)]
  [(fv_ (e_1 e_2)) (∪ (fv_ e_1) (fv_ e_2))]
  [(fv_ (λ x e))   (set-diff (fv_ e) (x))])
(define-metafunction λneed
  remove-duplicates : (x ...) -> (x ...)
  [(remove-duplicates ()) ()]
  [(remove-duplicates (x)) (x)]
  [(remove-duplicates (x_1 x_2 ...)) ; x \notin (x_2 ...)
   (x_1 ,@(term (remove-duplicates (x_2 ...))))
   (side-condition (not (memq (term x_1) (term (x_2 ...)))))]
  [(remove-duplicates (x_1 x_2 ...)) ; x \in (x_2 ...)
   (remove-duplicates (x_2 ...))
   (side-condition (memq (term x_1) (term (x_2 ...))))])
(define-metafunction λneed
  ∪ : (x ...) ... -> (x ...)
  [(∪ (x_1 ...) (x_2 ...) (x_3 ...) ...)
   (∪ (x_1 ... x_2 ...) (x_3 ...) ...)]
  [(∪ (x ...)) (x ...)]
  [(∪)         ()])
(define-metafunction λneed
  set-diff : (x ...) (x ...) -> (x ...)
  [(set-diff (x ...) ()) (x ...)]
  [(set-diff (x_1 ... x_2 x_3 ...) (x_2 x_4 ...))
   (set-diff (x_1 ... x_3 ...) (x_4 ...))
   (side-condition (not (memq (term x_2) (term (x_1 ... x_3 ...)))))]
  [(set-diff (x_1 ... x_2 x_3 ...) (x_2 x_4 ...))
   (set-diff (x_1 ... x_3 ...) (x_2 x_4 ...))
   (side-condition (memq (term x_2) (term (x_1 ... x_3 ...))))]
  [(set-diff (x_1 ...) (x_2 x_3 ...))
   (set-diff (x_1 ...) (x_3 ...))
   (side-condition (not (memq (term x_2) (term (x_1 ...)))))])
(define (close e)
  (define (make-x i)
    (string->symbol (string-append "x_" (number->string i))))
  (let ([fvs (term (fv ,e))])
    (let L ([e (term (rename-bound-vars ,e ,(append fvs (term (bound-vars ,e)))))]
            [fvs fvs] [i 1])
      (if (empty? fvs)
          e
          (let ([x (make-x i)])
            (L (term ((λ ,(first fvs) ,e) (λ ,x ,x))) 
               (rest fvs) (add1 i)))))))

(define-metafunction λneed-ck
  [(alpha-equiv? c_1 c_2) (alphaeq c_1 c_2 () ())])
(define-metafunction λneed-ck
  [(alphaeq (λ x_1 c_1) (λ x_2 c_2) (x_3 ...) (x_4 ...))
   (alphaeq c_1 c_2 (x_1 x_3 ...) (x_2 x_4 ...))]
  [(alphaeq (c_1 c_2) (c_3 c_4) (x_1 ...) (x_2 ...))
   ,(and (term (alphaeq c_1 c_3 (x_1 ...) (x_2 ...)))
         (term (alphaeq c_2 c_4 (x_1 ...) (x_2 ...))))]
  [(alphaeq x_1 x_2 (x_3 ...) (x_4 ...))
   ,(= (length (member (term x_1) (term (x_3 ...))))
       (length (member (term x_2) (term (x_4 ...)))))]
  [(alphaeq any_1 any_2 any_3 any_4) #f])
(define-metafunction λneed-ck
  [(extract-bindings c) (get-bindings c ())])
(define-metafunction λneed-ck
  [(get-bindings ((λ x c_1) c_2) ((x_1 c) ...))
   (get-bindings c_1 ((x c_2) (x_1 c) ...))]
  [(get-bindings (λ x c) ((x_1 c_1) ...))
   ((x_1 c_1) ...)])

(define-metafunction λneed-ck
  [(lazystep-equal? (in-hole L_1 v_1) (in-hole L_2 v_2))
   (alpha-equiv? v_1 v_2)]
  [(lazystep-equal? (lab x_1 c_1) (lab x_2 c_2))
   (lazystep-equal? c_1 c_2)]
  [(lazystep-equal? (c_1 c_2) (c_3 c_4))
   ,(and (term (lazystep-equal? c_1 c_3))
         (term (lazystep-equal? c_2 c_4)))]
  [(lazystep-equal? any_1 any_2)
   ,(equal? (term any_1) (term any_2))])

(define-metafunction λneed-ck
  ψ : (e (F ...)) -> c ; lazystep term
  [(ψ (e (F ...))) (ψ_ (F ...) e)])
(define-metafunction λneed-ck
  ψ_ : (C ...) c -> c
  [(ψ_ (mt) c) c]
  [(ψ_ ((lam x) C_1 ... (arg c_1) C_2 ...) c)
   (ψ_ (C_1 ... C_2 ...) (subst c x (lab x c_1)))
   (side-condition (redex-match λneed A (term (φK (C_1 ...)))))]
  [(ψ_ ((arg c_1) C ...) c) 
   (ψ_ (C ...) (c c_1))]
  [(ψ_ ((body x (C_1 ...) (C_2 ...)) C ...) c)
   (ψ_ (C_1 ... (lam x) C_2 ... (arg c) C ...) x)])

(define-metafunction λneed-ck
  strip-v-labs : c -> c
  [(strip-v-labs (in-hole L (c_1 c_2))) (in-hole L ((strip-v-labs c_1) 
                                                    (strip-v-labs c_2)))]
  [(strip-v-labs (in-hole L (λ x c))) (λ x (strip-v-labs c))]
  [(strip-v-labs (in-hole L x)) (in-hole L x)]
  [(strip-v-labs x_1) x_1]
  [(strip-v-labs (c_1 c_2)) ((strip-v-labs c_1)
                             (strip-v-labs c_2))]
  [(strip-v-labs (λ x c)) (λ x (strip-v-labs c))])
(define-metafunction λneed-ck
  strip-labs : c -> c
  [(strip-labs (lab x c)) (strip-labs c)]
  [(strip-labs (c_1 c_2)) ((strip-labs c_1) (strip-labs c_2))]
  [(strip-labs (λ x c)) (λ x (strip-labs c))]
  [(strip-labs x) x])

#;(define (CF-CK-bisim? t)
  (printf "~a) checking: ~a\n" n t)
  (set! n (add1 n))
  (let loop ([t (term (,t (mt)))])
;    (printf "t = ~a\n" t)
    (let ([res1 (apply-reduction-relation red-ck t)])
      (cond
        [(null? res1)
         (redex-match λneed a (term (φ ,t)))]
        [(= (length res1) 1)
         (if (term (alpha-equiv? (φ ,(car res1)) (φ ,t)))
             (loop (car res1))
             (let ([res2 (apply-reduction-relation red (term (φ ,t)))])
               (if (term (alpha-equiv? (φ ,(car res1)) ,(car res2)))
                   (loop (car res1))
                   #f)))]
        [else #f]))))
(define (CK-lazystep-bisim? t)
  (printf "~a) checking: ~a\n" n t)
  (set! n (add1 n))
  (let loop ([t (term (,t (mt)))])
    (let ([res1 (apply-reduction-relation red-ck t)])
      (cond
        [(null? res1)
         (redex-match λneed a (term (φ ,t)))]
        [(= (length res1) 1)
         (if (or (term (alpha-equiv? (strip-labs (ψ ,(car res1)))
                                     (strip-labs (ψ ,t))))
                 #;(redex-match λneed-ck (in-hole L v) (term (ψ ,t)))
                 (let ([res2 (apply-reduction-relation lazystep-red (term (ψ ,t)))])
                   (and (not (null? res2))
                        (= (length res2) 1)
;                        (printf "(ψ t)          = ~a\n" (term (ψ ,t)))
;                        (printf "(ψ (car res1)) = ~a\n" (term (ψ ,(car res1))))
;                        (printf "(car res2)     = ~a\n" (car res2))
                        (term (alpha-equiv? (strip-labs (ψ ,(car res1)))
                                            (strip-labs ,(car res2)))))))
               (loop (car res1))
               (and (let ([res2 (apply-reduction-relation lazystep-red (term (ψ ,t)))])
                      (printf "failed1:\nt = ~a\nres1 = ~a\n(ψ t) =    ~a\n(ψ res1) = ~a\nres2 =     ~a\n" 
                              t (car res1) 
                              (term (strip-labs (ψ ,t))) 
                              (term (strip-labs (ψ ,(car res1))))
                              (term (strip-labs ,(car res2)))))
                    #f))]
        [else (and (printf "failed2: ~a\n" t)
                   #f)]))))
#;(define (gen-trace-ck t)
  (define (gen-trace-ck-help t)
    (let ([res (apply-reduction-relation red-ck t)])
          (if (null? res)
              (list t)
              (cons t (gen-trace-ck-help (car res))))))
  (gen-trace-ck-help (term (,t (mt)))))
(define n 1)
(define-syntax (redex-check-go stx)
  (syntax-case stx ()
    [(_) #'(redex-check λneed e (CK-lazystep-bisim? (term e))
                        #:prepare close 
                        #:attempts 1000000)]))
(define-syntax (traces-ck stx)
  (syntax-case stx ()
  [(_ red t) #'(traces red (term (,t (mt))))]))
;(redex-check-go)