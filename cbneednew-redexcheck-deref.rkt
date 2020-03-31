#lang racket
(require redex)
(require "cbneednew-deref.rkt")
(require "../cbneed/call-by-need-feng.ss")

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
    (let L ([e e] [fvs fvs] [i 1])
      (if (empty? fvs)
          e
          (let ([x (make-x i)])
            (L (term ((λ ,(first fvs) ,e) (λ ,x ,x))) 
               (rest fvs) (add1 i)))))))

(define-metafunction λneed
  [(alpha-equiv? e_1 e_2) (alphaeq e_1 e_2 () ())])
(define-metafunction λneed
  [(alphaeq (λ x_1 e_1) (λ x_2 e_2) (x_3 ...) (x_4 ...))
   (alphaeq e_1 e_2 (x_1 x_3 ...) (x_2 x_4 ...))]
  [(alphaeq (e_1 e_2) (e_3 e_4) (x_1 ...) (x_2 ...))
   ,(and (term (alphaeq e_1 e_3 (x_1 ...) (x_2 ...)))
         (term (alphaeq e_2 e_4 (x_1 ...) (x_2 ...))))]
  [(alphaeq x_1 x_2 (x_3 ...) (x_4 ...))
   ,(= (length (member (term x_1) (term (x_3 ...))))
       (length (member (term x_2) (term (x_4 ...)))))]
  [(alphaeq any_1 any_2 any_3 any_4) #f])
(define-metafunction λneed
  [(extract-bindings e) (get-bindings e ())])
(define-metafunction λneed
  [(get-bindings ((λ x e_1) e_2) ((x_1 e) ...))
   (get-bindings e_1 ((x e_2) (x_1 e) ...))]
  [(get-bindings (λ x e) ((x_1 e_1) ...))
   ((x_1 e_1) ...)])
(define (AF-equiv-noambig? t)
  (printf "~a) checking: ~a\n" n t)
  (set! n (add1 n))
  (let ([res1 (apply-red-no-ambig* red t)]
        [res2 (apply-red-no-ambig* λ-need-red-alpha t)])
    (and (redex-match λneed a res1)
         (redex-match λ-need A res2)
         (let ([res3 (apply-red-no-ambig* λ-need-red-nobeta res1)])
           (redex-match λ-need A res3)
           (term (alpha-equiv? ,res2 ,res3))))))
(define n 1)
(define-syntax (redex-check-go stx)
  (syntax-case stx ()
    [(_) #'(redex-check λneed e (AF-equiv-noambig? (term e)) 
                        #:prepare close 
                        #:attempts 1000000)]))

(redex-check-go)