#lang plai-typed
(require plai-typed/s-exp-match
         "class.rkt"
         "inherit.rkt"
         "typed-class.rkt"
         "inherit-parse.rkt")

(module+ test
  (print-only-errors true))

;; ----------------------------------------

(define (parse-t-class [s : s-expression]) : ClassT
  (cond
   [(s-exp-match? `{class SYMBOL extends SYMBOL {ANY ...} ANY ...} s)
    (classT (s-exp->symbol (second (s-exp->list s)))
            (s-exp->symbol (fourth (s-exp->list s)))
            (map parse-t-field
                 (s-exp->list (fourth (rest (s-exp->list s)))))
            (map parse-t-method 
                 (rest (rest (rest (rest (rest (s-exp->list s))))))))]
   [else (error 'parse-t-class "invalid input")]))

(define (parse-t-field [s : s-expression]) : FieldT
  (cond
   [(s-exp-match? `[SYMBOL : ANY] s)
    (fieldT (s-exp->symbol (first (s-exp->list s)))
            (parse-type (third (s-exp->list s))))]
   [else (error 'parse-t-field "invalid input")]))

(define (parse-t-method [s : s-expression]) : MethodT
  (cond
   [(s-exp-match? `{SYMBOL : ANY -> ANY ANY} s)
    (methodT (s-exp->symbol (first (s-exp->list s)))
             (parse-type (third (s-exp->list s)))
             (parse-type (fourth (rest (s-exp->list s))))
             (parse (fourth (rest (rest (s-exp->list s))))))]
   [else (error 'parse-t-method "invalid input")]))

(define (parse-type [s : s-expression]) : Type
  (cond
    [(s-exp-match? `{arr ANY} s)
     (arrT (parse-obj-type (second (s-exp->list s))))]
    [(s-exp-match? `num s)
     (numT)]
    [(s-exp-match? `SYMBOL s)
     (objT (s-exp->symbol s))]
    [else (error 'parse-type "invalid input")]))

(define (parse-obj-type [s : s-expression]) : Type
  (cond
    [(s-exp-match? `SYMBOL s)
     (objT (s-exp->symbol s))]
    [else (error 'parse-type "invalid input")]))

(module+ test
  (test (parse-type `num)
        (numT))
  (test (parse-type `object)
        (objT 'object))
  (test (parse-type `{arr num})
        (arrT (objT 'num))) ; num class shadows built-in num -- object arrays only
  (test/exn (parse-type `{arr {arr {arr object}}})
            "invalid input") ; nesting not allowed
  (test/exn (parse-type `{})
            "invalid input")
  
  (test (parse-t-field `[x : num])
        (fieldT 'x (numT)))
  (test/exn (parse-t-field '{x 1})
            "invalid input")

  (test (parse-t-method `{m : num -> object this})
        (methodT 'm (numT) (objT 'object) (thisI)))
  (test/exn (parse-t-method `{m 1})
            "invalid input")
  
  (test (parse-t-class '{class posn3D extends posn
                               {[x : num] [y : num]}
                               {m1 : num -> num arg}
                               {m2 : num -> object this}})
        (classT 'posn3D 'posn
                (list (fieldT 'x (numT))
                      (fieldT 'y (numT)))
                (list (methodT 'm1 (numT) (numT) (argI))
                      (methodT 'm2 (numT) (objT 'object) (thisI)))))
  (test/exn (parse-t-class '{class})
            "invalid input"))

;; ----------------------------------------

(define (interp-t-prog [classes : (listof s-expression)] [a : s-expression]) : s-expression
  (let ([v (interp-t (parse a)
                     (map parse-t-class classes))])
    (type-case Value v
      [numV (n) (number->s-exp n)]
      [objV (class-name field-vals) `object]
      [nullV () `null]
      [arrV (type-name vals) `array])))

(module+ test
  (test (interp-t-prog
         (list
          '{class empty extends object
             {}})
         '{new empty})
        `object)

  (define posn-t-class
    '{class posn extends object
             {[x : num]
              [y : num]}
             {mdist : num -> num
                    {+ {get this x} {get this y}}}
             {addDist : posn -> num
                      {+ {send arg mdist 0}
                         {send this mdist 0}}}})
  (define posn3D-t-class
    '{class posn3D extends posn
             {[z : num]}
             {mdist : num -> num
                    {+ {get this z} 
                       {super mdist arg}}}})

  (test (interp-t-prog 
         (list posn-t-class posn3D-t-class)
         '{send {set {set {set {new posn3D} x 5} y 3} z 1} addDist {set {set {new posn} x 2} y 7}})
        '18)

  (test (interp-t-prog
         (list posn-t-class posn3D-t-class)
         '{if0 {+ {send {cast posn {set {set {set {new posn3D} x 5} y 3} z 1}} mdist null} -9}
               null
               {set {set {new posn} x 2} y 2}})
        `null)

  (test (interp-t-prog
         (list posn-t-class)
         '{newarray posn 5 {set {new posn} x 5}})
        `array)

  (test (interp-t-prog
         (list posn-t-class
               posn3D-t-class
               '{class tester extends object
                  {[x : {arr posn}]}
                  {update : posn -> num
                          {arrayset {get this x} 3 arg}}})
         '{send
           {set
            {new tester}
            x
            {newarray posn3D 5 {set {set {set {new posn3D} x 5} y 3} z 1}}}
           update
           {new posn3D}})
        '0)

  (test/exn (interp-t-prog
             (list posn-t-class
                   posn3D-t-class
                   '{class tester extends object
                      {[x : {arr posn}]}
                      {update : posn -> num
                              {arrayset {get this x} 3 arg}}})
             '{send
               {set
                {new tester}
                x
                {newarray posn3D 5 {set {set {set {new posn3D} x 5} y 3} z 1}}}
               update
               {new posn}})
            "array type violation"))

;; -----------------------------------------

(define (run-prog [classes : (listof s-expression)] [a : s-expression]) : Value
  (let [(prog (parse a))
        (classes (map parse-t-class classes))]
    (begin
      (typecheck prog classes)
      (interp-t prog classes))))

(module+ test
  (test/exn (run-prog
             (list)
             '{send this method 5})
            "this not bound")

  (test/exn (run-prog
             (list posn-t-class)
             '{send (new posn) mdist arg})
            "arg not bound")

  (test/exn (run-prog 
             (list posn-t-class posn3D-t-class)
             '{cast posn3D {set {set {new posn} x 2} y 7}})
            "cast failed")
  
  (test (run-prog 
         (list posn-t-class posn3D-t-class)
         '{send {set {set {set {new posn3D} x 5} y 3} z 1} addDist
                {cast posn {set {set {set {new posn3D} x 2} y 7} z 1}}})
        (numV 19))
  
  (test (run-prog
         (list posn-t-class
               posn3D-t-class
               '{class tester extends object
                  {[x : {arr posn}]}
                  {update : posn -> num
                          {arrayset {get this x} 3 arg}}
                  {test : tester -> {arr posn}
                        {if0 {send arg update {new posn3D}}
                             {get arg x}
                             null}}})
         
         '{send {new tester} test {set
                                   {new tester}
                                   x
                                   {newarray posn3D 5 {set {set {set {new posn3D} x 5} y 3} z 1}}}})
        
        (arrV 'posn3D (list (box (objV 'posn3D (list (box (numV 5)) (box (numV 3)) (box (numV 1)))))
                            (box (objV 'posn3D (list (box (numV 5)) (box (numV 3)) (box (numV 1)))))
                            (box (objV 'posn3D (list (box (numV 5)) (box (numV 3)) (box (numV 1)))))
                            (box (objV 'posn3D (list (box (numV 0)) (box (numV 0)) (box (numV 0)))))
                            (box (objV 'posn3D (list (box (numV 5)) (box (numV 3)) (box (numV 1)))))))))
