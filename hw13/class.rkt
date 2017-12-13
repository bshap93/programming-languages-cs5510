#lang plai-typed

(define-type ExprC
  [numC (n : number)]
  [plusC (lhs : ExprC)
         (rhs : ExprC)]
  [multC (lhs : ExprC)
         (rhs : ExprC)]
  [argC]
  [thisC]
  [newC (class-name : symbol)]
  [getC (obj-expr : ExprC)
        (field-name : symbol)]
  [setC (obj-expr : ExprC)
        (field-name : symbol)
        (arg-expr : ExprC)]
  [sendC (obj-expr : ExprC)
         (method-name : symbol)
         (arg-expr : ExprC)]
  [ssendC (obj-expr : ExprC)
          (class-name : symbol)
          (method-name : symbol)
          (arg-expr : ExprC)]
  [castC (type-name : symbol)
         (arg-expr : ExprC)]
  [if0C (tst : ExprC)
        (thn : ExprC)
        (els : ExprC)]
  [nullC]
  [newarrayC (type-name : symbol)
             (size : ExprC)
             (init-expr : ExprC)]
  [arrayrefC (array : ExprC)
             (index : ExprC)]
  [arraysetC (array : ExprC)
             (index : ExprC)
             (arg-expr : ExprC)])

(define-type ClassC
  [classC (name : symbol)
          (super-name : symbol)
          (fields : (listof FieldC))
          (methods : (listof MethodC))])

(define-type FieldC
  [fieldC (name : symbol)
          (type : BaseType)])

(define-type MethodC
  [methodC (name : symbol)
           (body-expr : ExprC)])

(define-type BaseType
  [numBT]
  [objBT]
  [arrBT (sub : BaseType)])

(define (base-type->default-val bt)
  (type-case BaseType bt
    [numBT () (numV 0)]
    [objBT () (nullV)]
    [arrBT (sub) (nullV)]))

(define-type Value
  [numV (n : number)]
  [objV (class-name : symbol)
        (field-values : (listof (boxof Value)))]
  [arrV (type-name : symbol)
        (values : (listof (boxof Value)))]
  [nullV])

(module+ test
  (print-only-errors true))

;; ----------------------------------------

(define (make-find [name-of : ('a -> symbol)])
  (lambda ([name : symbol] [vals : (listof 'a)]) : 'a
    (cond
     [(empty? vals)
      (error 'find "not found")]
     [else (if (equal? name (name-of (first vals)))
               (first vals)
               ((make-find name-of) name (rest vals)))])))

(define find-class : (symbol (listof ClassC) -> ClassC)
  (make-find classC-name))

(define find-method : (symbol (listof MethodC) -> MethodC)
  (make-find methodC-name))

;; A non-list pair:
(define-type (Pair 'a 'b)
  [kons (first : 'a) (rest : 'b)])

(define (get-field [name : symbol] 
                   [fields : (listof FieldC)]
                   [vals : (listof (boxof Value))])
  ;; Pair fields and values, find by field name,
  ;; then extract value from pair
  (kons-rest ((make-find (lambda (el) (fieldC-name (kons-first el))))
              name
              (map2 kons fields vals))))

(module+ test
  (test/exn (find-class 'a empty)
            "not found")
  (test (find-class 'a (list (classC 'a 'object empty empty)))
        (classC 'a 'object empty empty))
  (test (find-class 'b (list (classC 'a 'object empty empty)
                             (classC 'b 'object empty empty)))
        (classC 'b 'object empty empty))
  (test (get-field 'a 
                   (list (fieldC 'a (numBT)) (fieldC 'b (numBT)))
                   (list (box (numV 0)) (box (numV 1))))
        (box (numV 0))))

;; ----------------------------------------

(define interp : (ExprC (listof ClassC) Value Value -> Value)
  (lambda (a classes this-val arg-val)
    (local [(define (recur expr)
              (interp expr classes this-val arg-val))
            (define (array-op array index func)
              (type-case Value (recur index)
                [numV (idx) (if (< idx 0)
                                (error 'interp "index out of bounds")
                                (local [(define arr-val (recur array))]
                                  (type-case Value arr-val
                                    [arrV (type-name vals) (func type-name vals idx)]
                                    [else (error 'interp "not an array")])))]
                [else (error 'interp "not a number")]))]
      (type-case ExprC a
        [numC (n) (numV n)]
        [plusC (l r) (num+ (recur l) (recur r))]
        [multC (l r) (num* (recur l) (recur r))]
        [thisC () this-val]
        [argC () arg-val]
        [newC (class-name)
              (objV class-name (map (lambda (el)
                                      (box (base-type->default-val (fieldC-type el))))
                                    (classC-fields (find-class class-name classes))))]
        [getC (obj-expr field-name)
              (unbox (get-field-box (recur obj-expr) field-name classes))]
        [setC (obj-expr field-name arg-expr)
              (let [(obj-val (recur obj-expr))]
                (begin
                  (set-box! (get-field-box obj-val field-name classes) (recur arg-expr))
                  obj-val))] ; returns object value
        [sendC (obj-expr method-name arg-expr)
               (local [(define obj (recur obj-expr))
                       (define arg-val (recur arg-expr))]
                 (type-case Value obj
                   [objV (class-name field-vals)
                         (call-method class-name method-name classes
                                      obj arg-val)]
                   [else (error 'interp "not an object")]))]
        [ssendC (obj-expr class-name method-name arg-expr)
                (local [(define obj (recur obj-expr))
                        (define arg-val (recur arg-expr))]
                  (call-method class-name method-name classes
                               obj arg-val))]
        [castC (type-name arg-expr)
               (local [(define arg (recur arg-expr))]
                 (type-case Value arg
                   [objV (class-name field-vals)
                         (if (is-instance class-name type-name classes)
                             arg
                             (error 'interp "cast failed"))]
                   [nullV () arg] ; null is considered a valid instance of any type
                   [else (error 'interp "cast failed")]))]
        [if0C (tst thn els)
              (if (num-zero? (recur tst))
                  (recur thn)
                  (recur els))]
        [nullC () (nullV)]
        [newarrayC (type-name size init-expr)
                   (type-case Value (recur size)
                     [numV (n) (if (< n 0)
                                   (error 'interp "negative size array")
                                   (arrV type-name (init-array n (recur init-expr))))]
                     [else (error 'interp "not a number")])]
        [arrayrefC (array index)
                   (array-op array index
                             (lambda (type-name vals idx) (array-get vals idx)))]
        [arraysetC (array index arg-expr)
                   (array-op array index
                             (lambda (type-name vals idx) (local [(define arg-val (recur arg-expr))]
                                                  (type-case Value arg-val
                                                    [objV (class-name field-vals)
                                                          (if (is-instance class-name type-name classes)
                                                              (begin
                                                                (array-set vals idx arg-val)
                                                                (numV 0))
                                                              (error 'interp "array type violation"))]
                                                    [else (error 'interp "not an object")]))))]))))

(define (init-array size init-val)
  (cond
    [(equal? size 0) empty]
    [else (cons (box init-val) (init-array (- size 1) init-val))]))

(define (array-search vals idx func)
  (cond
    [(empty? vals) (error 'interp "index out of bounds")]
    [(equal? idx 0) (func (first vals))]
    [else (array-search (rest vals) (- idx 1) func)]))

(define (array-get vals idx)
  (array-search vals idx (lambda (b) (unbox b))))

(define (array-set vals idx arg-val)
  (array-search vals idx (lambda (b) (set-box! b arg-val))))

(define (get-field-box [obj-val : Value] [field-name : symbol] [classes : (listof ClassC)]) : (boxof Value) 
  (type-case Value obj-val
    [objV (class-name field-vals)
          (type-case ClassC (find-class class-name classes)
            [classC (name super-name fields methods)
                    (get-field field-name fields field-vals)])]
    [else (error 'interp "not an object")]))

(define (is-instance [class-name : symbol] [ancestor-name : symbol] [classes : (listof ClassC)]) : boolean
  (cond
    [(equal? class-name ancestor-name) #t]
    [(equal? class-name 'object) #f]
    [else (type-case ClassC (find-class class-name classes)
            [classC (name super-name fields methods)
                    (is-instance super-name ancestor-name classes)])]))

(define (call-method class-name method-name classes
                     obj arg-val)
  (type-case ClassC (find-class class-name classes)
    [classC (name super-name fields methods)
            (type-case MethodC (find-method method-name methods)
              [methodC (name body-expr)
                       (interp body-expr
                               classes
                               obj
                               arg-val)])]))

(define (num-op [op : (number number -> number)]
                [op-name : symbol] 
                [x : Value]
                [y : Value]) : Value
  (cond
    [(and (numV? x) (numV? y))
     (numV (op (numV-n x) (numV-n y)))]
    [else (error 'interp "not a number")]))

(define (num+ x y) (num-op + '+ x y))
(define (num* x y) (num-op * '* x y))
(define (num-zero? x)
  (cond
    [(numV? x) (equal? (numV-n x) 0)]
    [else (error 'interp "not a number")]))

;; ----------------------------------------
;; Examples

(module+ test
  (define posn-class
    (classC 
     'posn
     'object
     (list (fieldC 'x (numBT))
           (fieldC 'y (numBT)))
     (list (methodC 'mdist
                    (plusC (getC (thisC) 'x) (getC (thisC) 'y)))
           (methodC 'addDist
                    (plusC (sendC (thisC) 'mdist (numC 0))
                           (sendC (argC) 'mdist (numC 0))))
           (methodC 'addX
                    (plusC (getC (thisC) 'x) (argC)))
           (methodC 'multY (multC (argC) (getC (thisC) 'y)))
           (methodC 'factory12 (setC (setC (newC 'posn) 'x (numC 1)) 'y (numC 2))))))

  (define posn3D-class
    (classC 
     'posn3D
     'posn
     (list (fieldC 'x (numBT))
           (fieldC 'y (numBT))
           (fieldC 'z (numBT)))
     (list (methodC 'mdist (plusC (getC (thisC) 'z)
                                  (ssendC (thisC) 'posn 'mdist (argC))))
           (methodC 'addDist (ssendC (thisC) 'posn 'addDist (argC))))))

  (define setC-test-class
    (classC
     'setC-tester
     'object
     (list (fieldC 'x (objBT)) (fieldC 'arr (arrBT (numBT))))
     (list (methodC 'test (if0C (getC (setC (argC) 'x (numC 0)) 'x)
                                (argC) ; same arg-val, but field should be updated
                                (nullC))))))

  (define arraysetC-test-class
    (classC
     'array-tester
     'object
     (list (fieldC 'idx (numBT)) (fieldC 'val (arrBT (objBT))))
     (list (methodC 'test (if0C (arraysetC (argC) (getC (thisC) 'idx) (getC (thisC) 'val))
                                (argC) ; same array, but val at position should be updated
                                (nullC))))))

  (define posn27 (setC (setC (newC 'posn) 'x (numC 2)) 'y (numC 7)))
  (define posn531 (setC (setC (setC (newC 'posn3D) 'x (numC 5)) 'y (numC 3)) 'z (numC 1)))
  (define setctester (newC 'setC-tester))
  (define arraytester (newC 'array-tester))

  (define (interp-posn a)
    (interp a (list posn-class posn3D-class arraysetC-test-class) (numV -1) (numV -1)))

  (define (interp-default a)
    (interp a (list) (numV -1) (numV -1))))

;; ----------------------------------------

(module+ test
  (test (interp (numC 10) 
                empty (numV -1) (numV -1))
        (numV 10))
  (test (interp (plusC (numC 10) (numC 17))
                empty (numV -1) (numV -1))
        (numV 27))
  (test (interp (multC (numC 10) (numC 7))
                empty (numV -1) (numV -1))
        (numV 70))

  (test (interp-posn posn27)
        (objV 'posn (list (box (numV 2)) (box (numV 7)))))

  (test (interp-posn (sendC posn27 'mdist (numC 0)))
        (numV 9))
  
  (test (interp-posn (sendC posn27 'addX (numC 10)))
        (numV 12))

  (test (interp-posn (sendC (ssendC posn27 'posn 'factory12 (numC 0))
                            'multY
                            (numC 15)))
        (numV 30))

  (test (interp-posn (sendC posn531 'addDist posn27))
        (numV 18))
  
  (test/exn (interp-posn (plusC (numC 1) posn27))
            "not a number")
  (test/exn (interp-posn (getC (numC 1) 'x))
            "not an object")
  (test/exn (interp-posn (sendC (numC 1) 'mdist (numC 0)))
            "not an object")
  (test/exn (interp-posn (ssendC (numC 1) 'posn 'mdist (numC 0)))
            "not an object")

  ; castC
  (test (interp-posn (castC 'posn posn27))
        (objV 'posn (list (box (numV 2)) (box (numV 7)))))
  (test (interp-posn (castC 'posn posn531))
        (objV 'posn3D (list (box (numV 5)) (box (numV 3)) (box (numV 1)))))
  (test (interp-posn (castC 'object posn531))
        (objV 'posn3D (list (box (numV 5)) (box (numV 3)) (box (numV 1)))))
  (test/exn (interp-posn (castC 'num (numC 1)))
            "cast failed") ; built-in num is not the same as 'num class
  (test/exn (interp-posn (castC 'posn3D posn27))
            "cast failed")
  (test/exn (interp-posn (castC 'object (numC 1)))
            "cast failed")

  ; if0C
  (test (interp-posn (if0C (numC 0) (numC 2) (numC 3)))
        (numV 2))
  (test (interp-posn (if0C (numC 1) (numC 2) (numC 3)))
        (numV 3))
  (test/exn (interp-posn (if0C posn27 (numC 2) (numC 3)))
            "not a number")

  ; nullC
  (test (interp-posn (nullC))
        (nullV))
  (test (interp-posn (setC (setC (newC 'posn) 'x (nullC)) 'y (nullC)))
        (objV 'posn (list (box (nullV)) (box (nullV)))))
  (test (interp-posn (sendC posn27 'mdist (nullC)))
        (numV 9))
  (test (interp-posn (castC 'posn (nullC)))
        (nullV))
  (test/exn (interp-posn (sendC (castC 'posn (nullC)) 'mdist (numC 0)))
            "not an object")
  (test/exn (interp-posn (getC (castC 'posn (nullC)) 'x))
            "not an object")

  ; setC
  (test (interp-posn (setC posn27 'x (numC 5)))
        (objV 'posn (list (box (numV 5)) (box (numV 7)))))
  (test (interp-posn (getC posn27 'x))
        (numV 2))
  (test (interp (sendC setctester 'test posn27) (list setC-test-class posn-class) (numV -1) (numV -1)) ; test imperative update
        (objV 'posn (list (box (numV 0)) (box (numV 7)))))
  (test/exn (interp-posn (setC posn27 'z (numC 3)))
            "not found")

  ; the new new
  (test (interp-posn (getC (newC 'posn) 'x))
        (numV 0))
  (test (interp (getC (newC 'setC-tester) 'x) (list setC-test-class) (numV -1) (numV -1))
        (nullV))

  ; arrays...
  (test (interp-posn (newarrayC 'posn (numC 2) posn27))
        (arrV 'posn (list (box (objV 'posn (list (box (numV 2)) (box (numV 7))))) (box (objV 'posn (list (box (numV 2)) (box (numV 7))))))))
  (test (interp-posn (newarrayC 'posn (numC 0) posn27))
        (arrV 'posn (list)))
  (test/exn (interp-posn (newarrayC 'posn (numC -1) posn27))
            "negative size array")
  (test/exn (interp-posn (newarrayC 'posn posn27 (numC 3)))
            "not a number")
  (test (interp-posn (arrayrefC (newarrayC 'posn (numC 8) posn27) (numC 5)))
        (objV 'posn (list (box (numV 2)) (box (numV 7)))))
  (test/exn (interp-default (arrayrefC (numC 1) (numC 8)))
            "not an array")
  (test/exn (interp-posn (arrayrefC (newarrayC 'posn (numC 8) posn27) (numC -1)))
            "index out of bounds")
  (test/exn (interp-posn (arrayrefC (newarrayC 'posn (numC 8) posn27) (numC 8)))
            "index out of bounds")
  (test/exn (interp-posn (arrayrefC (newarrayC 'posn (numC 8) posn27) posn27))
            "not a number")
  (test (interp-posn (arraysetC (newarrayC 'posn (numC 5) posn27) (numC 3) posn27))
        (numV 0))
  (test (interp-posn (sendC (setC (setC arraytester 'idx (numC 1)) 'val (newC 'posn)) 'test (newarrayC 'posn (numC 3) posn27)))
        (arrV 'posn (list (box (objV 'posn (list (box (numV 2)) (box (numV 7)))))
                          (box (objV 'posn (list (box (numV 0)) (box (numV 0)))))
                          (box (objV 'posn (list (box (numV 2)) (box (numV 7))))))))
  (test/exn (interp-posn (arraysetC (newarrayC 'posn (numC 5) posn27) (numC 3) (numC 2)))
            "not an object")
  (test/exn (interp-posn (arraysetC (newarrayC 'posn3D (numC 5) posn531) (numC 3) posn27))
            "array type violation"))
                      