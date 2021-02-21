#lang typed/racket
;;; Type
(define-type KeyWord (U '+ '- '* '/ '** '>= '> '= '< '<= 'dd '? '?v '?c))
(define-type Variable (Refine [var : Symbol] (! var KeyWord)))
(define-type Operator (U '+ '- '* '/ '** '>= '> '= '< '<= (List 'dd Variable)))
(define-type Math-Expression (U Variable Real (Pair Operator (Listof Math-Expression))))
(define-type POperator (U Operator (List 'dd (List '?v Variable))))
(define-type SOperator (U Operator (List 'dd (List ': Variable))))
(define-type Pattern (U (List '? Variable) (List '?c Variable) (List '?v Variable)
                        Math-Expression
                        (Pair POperator (Listof Pattern))))
(define-type Skeleton (U (List ': Variable)
                         Math-Expression
                         (Pair SOperator (Listof Skeleton))))
(define-type Dictionary (Option (Listof (List Variable Math-Expression))))
(define-type Rule (List Pattern Skeleton))


;;; Predicate
(define-predicate variable? Variable)
(define-predicate math-expression? Math-Expression)
(define-predicate operator? Operator)
(define-predicate poperator? POperator)
(define-predicate soperator? SOperator)
(define-predicate pattern? Pattern)
(define-predicate skeleton? Skeleton)
(define-predicate rule? Rule)
(define-predicate ?c? (List '?c Variable))
(define-predicate ?v? (List '?v Variable))
(define-predicate ?? (List '? Variable))
(define-predicate :? (List ': Variable))
(define-predicate dictionary? Dictionary)
(define-predicate special-pattern? (Pair POperator (Listof Pattern)))
(define-predicate special-skeleton? (Pair SOperator (Listof Skeleton)))
(define-predicate special-math-exp? (Pair Operator (Listof Math-Expression)))


;;; Matcher
(: matcher [-> Pattern Math-Expression Dictionary Dictionary])
(define (matcher pattern expression dictionary)
  (cond [(false? dictionary) #f]
        [(and (math-expression? pattern) (equal? pattern expression)) dictionary]
        [(and (?c? pattern) (real? expression))
         (extend-dictionary pattern expression dictionary)]
        [(and (?v? pattern) (variable? expression))
         (extend-dictionary pattern expression dictionary)]
        [(and (?? pattern) (math-expression? expression))
         (extend-dictionary pattern expression dictionary)]
        [(and (special-pattern? pattern) (special-math-exp? expression))
         (: op Operator)
         (define op (car expression))
         (: p-op POperator)
         (define p-op (car pattern))
         (define-predicate p-dd? (List 'dd (List '?v Variable)))
         (define-predicate dd? (List 'dd Variable))
         (: init-dict Dictionary)
         (define init-dict
           (cond [(equal? op p-op) dictionary]
                 [(and (p-dd? p-op) (dd? op)) (matcher (cadr p-op) (cadr op) dictionary)]
                 [else #f]))
         (if (false? init-dict)
             #f
             (foldl matcher
                    init-dict
                    (cdr pattern)
                    (cdr expression)))]
        [else #f]))


;;; Dictionary
(: make-empty-dictionary [-> Null])
(define (make-empty-dictionary) '())
(: extend-dictionary [-> (U (List '? Variable) (List '?c Variable) (List '?v Variable))
                         Math-Expression Dictionary Dictionary])
(define (extend-dictionary pat dat dict)
  (cond [(false? dict) #f]
        [else
         (: vname Variable)
         (define vname (cadr pat))
         (: v (Option (List Variable Math-Expression)))
         (define v (assq vname dict))
         (cond [(false? v)
                (cons (ann (list vname dat)
                           (List Variable Math-Expression))
                      dict)]
               [(eq? (cadr v) dat) dict]
               [else #f])]))
(: apply-dict [-> Dictionary Variable (Option Math-Expression)])
(define (apply-dict dict var)
  (if (false? dict)
      #f
      (let ([ls : (Option (List Variable Math-Expression))
                (assq var dict)])
        (if (false? ls)
            #f
            (cadr ls)))))


;;; instantiate
(: instantiate [-> Skeleton Dictionary (Option Math-Expression)])
(define (instantiate skeleton dictionary)
  (: inst-map [-> [-> Skeleton (Option Math-Expression)] (Listof Skeleton)
                  (Option (Listof Math-Expression))])
  (define inst-map
    (λ (proc skts)
      (if (null? skts)
          '()
          (let ([exp : (Option Math-Expression)
                     (proc (car skts))])
            (if (false? exp)
                #f
                (let ([exps : (Option (Listof Math-Expression))
                            (inst-map proc (cdr skts))])
                  (if (false? exps)
                      #f
                      (cons exp exps))))))))
  (cond [(false? dictionary) #f]
        [(math-expression? skeleton) skeleton]
        [(:? skeleton) (apply-dict dictionary (cadr skeleton))]
        [(special-skeleton? skeleton)
         (: sop SOperator)
         (define sop (car skeleton))
         (: op (Option Operator))
         (define op
           (if (operator? sop)
               sop
               (let ([var : (Option Math-Expression)
                          (instantiate (cadr sop) dictionary)])
                 (if (variable? var)
                     (list 'dd var)
                     #f))))
         (if (false? op)
             #f
             (let ([exps : (Option (Listof Math-Expression))
                         (inst-map (ann (λ (skt) (instantiate skt dictionary))
                                        [-> Skeleton (Option Math-Expression)])
                                   (cdr skeleton))])
               (if (false? exps)
                   #f
                   (cons op exps))))]
        [else #f]))



(: simplfier [-> (Listof Rule) [-> Math-Expression Math-Expression]])
(define (simplfier rules)
  (: simplify-exp [-> Math-Expression Math-Expression])
  (define (simplify-exp exp)
    (try-rules
     (cond [(variable? exp) exp]
           [(real? exp) exp]
           [(special-math-exp? exp)
            (cons (car exp)
                  (map simplify-exp (cdr exp)))])))
  
  (: try-rules [-> Math-Expression Math-Expression])
  (define (try-rules exp)
    (: scan [-> (Listof Rule) Math-Expression])
    (define (scan the-rules)
      (cond [(null? the-rules) exp]
            [else
             (let ([dict : Dictionary
                         (matcher (caar the-rules)
                                  exp
                                  (make-empty-dictionary))])
               (if (false? dict)
                   (scan (cdr the-rules))
                   (let ([stepped-exp : (Option Math-Expression)
                                      (instantiate
                                          (cadar the-rules)
                                          dict)])
                     (if (math-expression? stepped-exp)
                         (simplify-exp stepped-exp)
                         (scan (cdr the-rules))))))]))
    (scan rules))
  simplify-exp)

(: deriv-rules (Listof Rule))
(define deriv-rules
  `(
        [((dd (?v v)) (?c c)) 0] 
        [((dd (?v v)) (?v v)) 1] 
        [((dd (?v v)) (?v u)) 0]
        [((dd (?v v)) (+ (? x1) (? x2))) 
         (+ ((dd (: v)) (: x1))
            ((dd (: v)) (: x2)))]
        [((dd (?v v)) (* (? x1) (? x2)))
         (+ (* (: x1) ((dd (: v)) (: x2)))
            (* ((dd (: v)) (: x1)) (: x2)))]
    ))

(: dsimp [-> Math-Expression Math-Expression])
(define dsimp (simplfier deriv-rules))





(: exp1 Math-Expression)
(define exp1 '((dd x) (* x x)))

(: exp2 Math-Expression)
(define exp2 '((dd x) (* x y)))

(: exp3 Math-Expression)
(define exp3 '((dd x) x))

(: exp4 Math-Expression)
(define exp4 '((dd x) 5))

(: exp5 Math-Expression)
(define exp5 '((dd x) (+ x (+ x 1))))

(: exp6 Math-Expression)
(define exp6 '((dd x) (+ (* 3 (- x 1)) (* (* 2 x) (* x (* 2 y))))))


(dsimp exp1)
(dsimp exp2)
(dsimp exp3)
(dsimp exp4)
(dsimp exp5)
(dsimp exp6)
