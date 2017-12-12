#lang plai-typed
(require plai-typed/s-exp-match
         "class.rkt"
         "inherit.rkt")

(module+ test
  (print-only-errors true))

;; ----------------------------------------

(define (parse-class [s : s-expression]) : ClassI
  (cond
   [(s-exp-match? `{class SYMBOL extends SYMBOL {ANY ...} ANY ...} s)
    (classI (s-exp->symbol (second (s-exp->list s)))
            (s-exp->symbol (fourth (s-exp->list s)))
            (map parse-field
                 (s-exp->list (fourth (rest (s-exp->list s)))))
            (map parse-method 
                 (rest (rest (rest (rest (rest (s-exp->list s))))))))]
   [else (error 'parse-class "invalid input")]))

(define (parse-field [s : s-expression]) : FieldC
  (cond
   [(s-exp-match? '[SYMBOL : ANY] s)
    (fieldC (s-exp->symbol (first (s-exp->list s)))
            (parse-basetype (third (s-exp->list s))))]
   [else (error 'parse-field "invalid input")]))

(define (parse-method [s : s-expression]) : MethodI
  (cond
   [(s-exp-match? `{SYMBOL ANY} s)
    (methodI (s-exp->symbol (first (s-exp->list s)))
             (parse (second (s-exp->list s))))]
   [else (error 'parse-method "invalid input")]))

(define (parse-basetype [s : s-expression]) : BaseType
  (cond
    [(s-exp-match? `num s)
     (numBT)]
    [(s-exp-match? `obj s)
     (objBT)]
    [else (error 'parse-basetype "invalid input")]))

(define (parse [s : s-expression]) : ExprI
  (cond
   [(s-exp-match? `NUMBER s) (numI (s-exp->number s))]
   [(s-exp-match? `arg s) (argI)]
   [(s-exp-match? `this s) (thisI)]
   [(s-exp-match? `null s) (nullI)]
   [(s-exp-match? '{+ ANY ANY} s)
    (plusI (parse (second (s-exp->list s)))
           (parse (third (s-exp->list s))))]
   [(s-exp-match? '{* ANY ANY} s)
    (multI (parse (second (s-exp->list s)))
           (parse (third (s-exp->list s))))]
   [(s-exp-match? '{new SYMBOL} s)
    (newI (s-exp->symbol (second (s-exp->list s))))]
   [(s-exp-match? '{get ANY SYMBOL} s)
    (getI (parse (second (s-exp->list s)))
          (s-exp->symbol (third (s-exp->list s))))]
   [(s-exp-match? '{set ANY SYMBOL ANY} s)
    (setI (parse (second (s-exp->list s)))
          (s-exp->symbol (third (s-exp->list s)))
          (parse (fourth (s-exp->list s))))]
   [(s-exp-match? '{send ANY SYMBOL ANY} s)
    (sendI (parse (second (s-exp->list s)))
           (s-exp->symbol (third (s-exp->list s)))
           (parse (fourth (s-exp->list s))))]
   [(s-exp-match? '{super SYMBOL ANY} s)
    (superI (s-exp->symbol (second (s-exp->list s)))
            (parse (third (s-exp->list s))))]
   [(s-exp-match? '{cast SYMBOL ANY} s)
    (castI (s-exp->symbol (second (s-exp->list s)))
           (parse (third (s-exp->list s))))]
   [(s-exp-match? '{if0 ANY ANY ANY} s)
    (if0I (parse (second (s-exp->list s)))
          (parse (third (s-exp->list s)))
          (parse (fourth (s-exp->list s))))]
   [else (error 'parse "invalid input")]))

(module+ test
  (test (parse '0)
        (numI 0))
  (test (parse `arg)
        (argI))
  (test (parse `this)
        (thisI))
  (test (parse '{+ 1 2})
        (plusI (numI 1) (numI 2)))
  (test (parse '{* 1 2})
        (multI (numI 1) (numI 2)))
  (test (parse '{new posn})
        (newI 'posn))
  (test (parse '{get 1 x})
        (getI (numI 1) 'x))
  (test (parse '{set 2 x 1})
        (setI (numI 2) 'x (numI 1)))
  (test (parse '{send 1 m 2})
        (sendI (numI 1) 'm (numI 2)))
  (test (parse '{super m 1})
        (superI 'm (numI 1)))
  (test (parse '{cast m 1})
        (castI 'm (numI 1)))
  (test (parse '{if0 0 1 2})
        (if0I (numI 0) (numI 1) (numI 2)))
  (test (parse `null)
        (nullI))
  (test/exn (parse `x)
            "invalid input")

  (test (parse-field `[x : num])
        (fieldC 'x (numBT)))
  (test (parse-field '[y : obj])
        (fieldC 'y (objBT)))
  (test/exn (parse-field '{x : 1})
            "invalid input")
  (test/exn (parse-field '{x 1})
            "invalid input")

  (test (parse-method `{m this})
        (methodI 'm (thisI)))
  (test/exn (parse-method `{m 1 2})
            "invalid input")
  
  (test (parse-class '{class posn3D extends posn
                             {[x : num] [y : num] [z : num]}
                             {m1 arg}
                             {m2 this}})
        (classI 'posn3D 'posn
                (list (fieldC 'x (numBT)) (fieldC 'y (numBT)) (fieldC 'z (numBT)))
                (list (methodI 'm1 (argI))
                      (methodI 'm2 (thisI)))))
  (test/exn (parse-class '{class})
            "invalid input"))

;; ----------------------------------------

(define (interp-prog [classes : (listof s-expression)] [a : s-expression]) : s-expression
  (let ([v (interp-i (parse a)
                     (map parse-class classes))])
    (type-case Value v
      [numV (n) (number->s-exp n)]
      [objV (class-name field-vals) `object]
      [nullV () `null])))

(module+ test
  (test (interp-prog
         (list
          '{class empty extends object
                  {}})
         '{new empty})
        `object)

 (test (interp-prog 
        (list
         '{class posn extends object
                 {[x : num] [y : num]}
                 {mdist {+ {get this x} {get this y}}}
                 {addDist {+ {send arg mdist 0}
                             {send this mdist 0}}}}
         
         '{class posn3D extends posn
                 {[z : num]}
                 {mdist {+ {get this z} 
                           {super mdist arg}}}})
        
        '{send {set {set {set {new posn3D} x 5} y 3} z 1} addDist {set {set {new posn} x 2} y 7}})
       '18)

  (test (interp-prog
         (list
          '{class posn extends object
                 {[x : num] [y : num]}
                 {mdist {+ {get this x} {get this y}}}
                 {addDist {+ {send arg mdist 0}
                             {send this mdist 0}}}})

         '{if0 {+ {send {cast posn {set {set {new posn} x 2} y 7}} mdist null} -9}
               null
               1})
        `null))

