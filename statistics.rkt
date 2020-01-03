#lang racket/base

;; You can require more modules of your choice.
(require racket/list
         racket/string
         (prefix-in utils: "utils.rkt"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                 ;;
;; Ciphertext Statistics                                                           ;;
;; =====================                                                           ;;
;;                                                                                 ;;
;; The module should provide a bunch of functions that do statistical analysis of  ;;
;; ciphertext. The output is almost always just an ordered list (counts are        ;;
;; omitted).                                                                       ;;
;;                                                                                 ;;
;; Fill in the body for the skeletons and do not change the arguments. You can     ;;
;; define as many functions as you require, there's no special credit for          ;;
;; implementing/using all of them.                                                 ;;
;;                                                                                 ;;
;; CAUTION:                                                                        ;;
;; 1. Be mindful that bi, tri and quadgrams do not cross word boundaries. Hence,   ;;
;; you must process each word separately.                                          ;;
;;                                                                                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Analyses
(provide cipher-monograms
         cipher-bigrams
         cipher-unique-neighbourhood
         cipher-neighbourhood
         cipher-trigrams
         cipher-quadgrams
         cipher-common-words-single
         cipher-common-words-double
         cipher-common-words-triple
         cipher-common-words-quadruple
         cipher-common-initial-letters
         cipher-common-final-letters
         cipher-common-double-letters
         cdr-str
         find-letter
         car-str
         sort-cdr
         ngrams
         cipher-ngrams
         count-sort
         count-sort2
         atoz
         fillzeroes
         numletters?
         last-str
         ;; any other functions of your design come below:

         ;; my-fundoo-analysis
         )

;; Takes ciphertext and produces a list of cipher chars sorted in decreasing
;; order of frequency.
(define (cipher-monograms ciphertext)
  (cipher-monograms-h ciphertext '()))

(define (cipher-monograms-h text collected)
  (cond
    [(not(non-empty-string? text)) (map (lambda (x) (car x)) (sort-cdr collected))]
    [(char-alphabetic? (car-str text)) (cipher-monograms-h (cdr-str text) (if(= (length collected) (find-letter (car-str text) collected)) (cons (cons (car-str text) 1) collected) (cons (cons (car (list-ref collected (find-letter (car-str text) collected))) (+ 1 (cdr (list-ref collected (find-letter (car-str text) collected))))) (remove (list-ref collected (find-letter (car-str text) collected)) collected)) ))]
    [else (cipher-monograms-h (cdr-str text) collected)]))

;; Takes the cipher-word-list and produces a list of 2-letter bigram (strings)
;; sorted in decreasing order of frequency. Each element must be a string!
(define (cipher-bigrams cipher-word-list)
  (cipher-ngrams cipher-word-list 2))

;; Takes the cipher-word-list and produces a list of 3-letter bigram (strings)
;; sorted in decreasing order of frequency. Each element must be a string!
(define (cipher-trigrams cipher-word-list)
  (cipher-ngrams cipher-word-list 3))

;; Takes the cipher-word-list and produces a list of 4-letter bigram (strings)
;; sorted in decreasing order of frequency. Each element must be a string!
(define (cipher-quadgrams cipher-word-list)
  (cipher-ngrams cipher-word-list 4))

;ABSTRACTED
(define (cipher-ngrams list n)
  (count-sort (foldr (lambda (x y) (append (ngrams n x) y)) '() list) '()))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;general use
(define (cdr-str str)
  (substring str 1 (string-length str)))
(define (find-letter char l)
  (find-letter-h char l 0))
(define (find-letter-h char l index)
  (cond
    [(= index (length l)) index]
    [(equal? char (car (list-ref l index))) index]
    [else (find-letter-h char l (+ index 1))]))
(define (car-str text)
  (string-ref text 0))
(define (sort-cdr l)
  (sort l (lambda (x y) (> (cdr x) (cdr y)))))
(define (count-sort2 l collected)
  (cond
    [(null? l) (sort-cdr collected)]
    [(= (length collected) (find-letter (car l) collected)) (count-sort2 (cdr l) (cons (cons (car l) 1) collected))]
    [else
     (count-sort2
      (cdr l)
      (cons
       (cons (car (list-ref collected (find-letter (car l) collected)))
             (+ 1 (cdr (list-ref collected (find-letter (car l) collected)))))
       (remove (list-ref collected (find-letter (car l) collected)) collected)))]))

(define atoz (build-list 26 (lambda(x) (integer->char (+ 97 x)))))

(define (fillzeroes lst)
  (fillzeroes-h lst atoz))
(define (fillzeroes-h lst set)
  (cond
    [(null? set) lst]
    [(= (length lst) (find-letter (car set) lst)) (fillzeroes-h (append lst (list (cons (car set) 0))) (cdr set))]
    [else (fillzeroes-h lst (cdr set))]))

(define (ngrams n str)
  (cond
    [(> n (string-length str)) '()]
    [else (cons (substring str 0 n) (ngrams n (cdr-str str)))]))

(define (count-sort l collected)
  (map (lambda(x) (car x)) (count-sort2 l collected)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Takes the bigram frequency order (output of `cipher-bigrams`) and computes
;; the neighbourhood of each letter with every other letter. Only unique
;; neighbours are to be counted.
;; Consider the character #\o.
;;
;; Takes an argument `mode`:
;; 1. (cipher-unique-neighbourhood cipher-bigrams 'predecessor)
;;    - Count only those unique occurrences where the (given) char preceeds
;;      other char.
;;    - Patterns of the form: "o?"
;; 2. (cipher-unique-neighbourhood cipher-bigrams 'successor)
;;    - Count only those unique occurrences where the (given) char succeeds
;;      other char.
;;    - Patterns of the form: "?o"
;; 3. (cipher-unique-neighbourhood cipher-bigrams 'both)
;;    - Count all unique occurrences where the (given) char neighbours the other
;;      char.
;;    - Patterns of the form "?o" and "o?". Note that this is not sum of (1) and
;;    (2) always.
;;
;; The output is a list of pairs of cipher char and the count of it's
;; neighbours. The list must be in decreasing order of the neighbourhood count.

;; You must match against or test (using cond) for the `mode` argument. Possibilities are:
  ;; 'predecessor, 'successor, 'both
;; Figure out experimentally which of these is a good indicator for E vs T it is 
(define (cipher-unique-neighbourhood cipher-bigrams-list mode)
  (fillzeroes (cond
                [(equal? mode 'predecessor)
                 (count-sort2 (foldr (lambda (x y) (cons (car-str x) y)) '() cipher-bigrams-list) '())]
                [(equal? mode 'successor)
     (count-sort2 (foldr (lambda (x y) (cons (car-str (cdr-str x)) y)) '() cipher-bigrams-list) '())]
                [else
                 (count-sort2
                  (foldr (lambda (x y)
               (if(equal? (car-str x) (car-str(cdr-str x)))
                  (cons (car-str x) y)
                  (cons (car-str x) (cons (car-str (cdr-str x)) y))))
                         '()
             cipher-bigrams-list)
                  '())])))
(define (pair-list-combine l1 l2)
  (cond
    [(null? l1) l1]
    [else (cons (cons (car (car l1)) (+ (cdr (car l1)) (cdr (car l2)))) (pair-list-combine (cdr l1) (cdr l2)))]))
(define (collect-bigrams lst)
  (foldr (lambda (x y) (append (ngrams 2 x) y)) '() lst))

;; Takes the bigram frequency order (output of `cipher-bigrams`) and computes
;; the neighbourhood of each letter with every other letter, but counts each
;; occurrence distinctly. This comment contains 6 bigrams with "w", all with "i" or "h".
;; So "w" has:
;; when mode is 'both,        6 neighbours
;; when mode is 'predecessor, 6 neighbours
;; when mode is 'successor,   0 neighbours
  ;; You must match against or test (using cond) for the `mode` argument. Possibilities are:
;; 'predecessor, 'successor, 'both
;; Figure out experimentally which of these is a good indicator for E vs T.
(define (cipher-neighbourhood cipher-word-list mode)
  (cipher-unique-neighbourhood (collect-bigrams cipher-word-list) mode))

;TRIGRAM ALREADY DEFINED

;QUADGRAM ALREADY DEFINED
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Takes the cipher word list and produces a list of single letter words, sorted
;; in decreasing order of frequency. Each element must be a string!
(define (cipher-common-words-single cipher-word-list)
  (cipher-common-words-ntuple cipher-word-list 1))

;; Takes the cipher word list and produces a list of double letter words, sorted
;; in decreasing order of frequency.
(define (cipher-common-words-double cipher-word-list)
  (cipher-common-words-ntuple cipher-word-list 2))

;; Takes the cipher word list and produces a list of triple letter words, sorted
;; in decreasing order of frequency.
(define (cipher-common-words-triple cipher-word-list)
  (cipher-common-words-ntuple cipher-word-list 3))

;; Takes the cipher word list and produces a list of four letter words, sorted
;; in decreasing order of frequency.
(define (cipher-common-words-quadruple cipher-word-list)
  (cipher-common-words-ntuple cipher-word-list 4))

;ABSTRACTED-common-ntuple
(define (cipher-common-words-ntuple cipher-word-list n)
  (count-sort (foldr (lambda (x y) (if(numletters? x n) (cons x y) y)) '() cipher-word-list) '()))
(define (numletters? str n)
  (= n (string-length str)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Takes the cipher word list and produces a list of chars that appear at the
;; start of words, sorted in decreasing order of frequency. Each element must be
;; a char!
(define (cipher-common-initial-letters cipher-word-list)
  (count-sort (foldr (lambda (x y) (cons (car-str x) y)) '() cipher-word-list) '()))

;; Takes the cipher word list and produces a list of chars that appear at the
;; end of words, sorted in decreasing order of frequency. Each element must be
;; a char!
(define (cipher-common-final-letters cipher-word-list)
  (count-sort (foldr (lambda (x y) (cons (last-str x) y)) '() cipher-word-list) '()))

;; Takes the cipher word list and produces a list of chars that appear as
;; consecutive double letters in some word, sorted in decreasing order of
;; frequency. Each element must thus be a char!
(define (cipher-common-double-letters cipher-word-list)
  (count-sort (foldr (lambda (x y) (append (take-double x '()) y)) '() cipher-word-list) '()))

(define (last-str str)
  (string-ref str (- (string-length str) 1)))

(define (take-double str ans)
  (cond
    [(or (= (string-length str) 1) (= (string-length str) 0)) ans]
    [(equal? (car-str str) (car-str (cdr-str str))) (take-double (cdr-str str) (cons (car-str str) ans))]
    [else (take-double (cdr-str str) ans)]))
;(cipher-bigrams utils:cipher-word-list)