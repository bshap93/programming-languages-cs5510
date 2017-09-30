#lang plai-typed

; recursive general form
(define (integer-power [x : number] [e : number]) : number
  (cond
    [(zero? e) 1]
    [(< e 0) (/ 1 (integer-power x (- 0 e)))]
    [else (* x (integer-power x (- e 1)))]))

(define (3rd-power [x : number]) : number
  (integer-power x 3))
(test (3rd-power 0) 0)
(test (3rd-power 1) 1)
(test (3rd-power -1) -1)
(test (3rd-power 2) 8)
(test (3rd-power 17) 4913)

(define (42nd-power [x : number]) : number
  (integer-power x 42))
(test (42nd-power 0) 0)
(test (42nd-power 1) 1)
(test (42nd-power -1) 1)
(test (42nd-power 2) 4398046511104)
(test (42nd-power 17) 4773695331839566234818968439734627784374274207965089)

; helper
(define (string-last-index [str : string]) : number
  (- (string-length str) 1))

; helper
(define (string-last [str : string]) : char
  (string-ref str (string-last-index str)))

(define (plural [str : string]) : string
  (cond
    [(equal? (string-length str) 0)
      "s"]
    [(equal? (string-last str) #\y)
      (string-append (substring str 0 (string-last-index str)) "ies")]
    [else
      (string-append str "s")]))
(test (plural "y") "ies")
(test (plural "") "s")
(test (plural "baby") "babies")
(test (plural "fish") "fishs")

(define-type Light
  [bulb (watts : number)
        (technology : symbol)]
  [candle (inches : number)])

(define (energy-usage [light : Light]) : number
  (type-case Light light
    [bulb (w t) (/ (* w 24) 1000)]
    [else 0]))
(test (energy-usage (bulb 100.0 'halogen)) 2.4)
(test (energy-usage (bulb 75 'led)) 1.8)
(test (energy-usage (candle 10.0)) 0)

(define (use-for-one-hour [light : Light]) : Light
  (type-case Light light
    [candle (i) (candle (max (- i 1) 0))]
    [bulb (w t) (bulb w t)]))
(test (use-for-one-hour (candle 2)) (candle 1))
(test (use-for-one-hour (candle 0)) (candle 0))
(test (use-for-one-hour (bulb 100 'halogen)) (bulb 100 'halogen))