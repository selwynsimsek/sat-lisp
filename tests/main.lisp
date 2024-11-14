(defpackage sat-lisp/tests/main
  (:use :cl
        :sat-lisp
        :rove))
(in-package :sat-lisp/tests/main)

;; NOTE: To run this test file, execute `(asdf:test-system :sat-lisp)' in your Lisp.

;; https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html

(deftest test-target-1
  (testing "should (= 1 1) to be true"
    (ok (= 1 1))))

(deftest start-solver
    (ok (with-sat-solver
            (check-sat))))

(deftest unsat
    (ok (not (with-sat-solver (add-literal 1)
               (add-literal 0)
               (add-literal -1)
               (add-literal 0)
               (check-sat)))))

;; (deftest de-morgan
;;   (ok (not (with-sat-solver
;;              (add-literal 1)
;;              (add-literal -2)
;;              (add-literal 0)
;;              (add-literal 2)
;;              (add-literal -1)
;;              (add-literal 0)
;;              (check-sat)))))

(deftest uf20-91
    (testing "testing uniform random 3-sat"
             (ok (loop for file in
                                (uiop:directory-files
                                 (asdf:system-relative-pathname :sat-lisp #p"tests/uf20-91/"))
                       always (let ((*debug-io* (make-string-output-stream))) (solve-cnf-file file))))))


(deftest bf
  (testing "testing bf"
    (ok (loop for file in
                       (uiop:directory-files
                        (asdf:system-relative-pathname :sat-lisp #p"tests/bf/"))
              never (let ((*debug-io* (make-string-output-stream))) (solve-cnf-file file))))))


(deftest dubois
  (testing "testing dubois"
    (ok (loop for file in
                       (uiop:directory-files
                        (asdf:system-relative-pathname :sat-lisp #p"tests/dubois/"))
              never (let ((*debug-io* (make-string-output-stream))) (solve-cnf-file file))))))

(deftest incremental
    (ok
     (loop repeat 10 always
       (with-sat-solver
           (add-literal 1)
         (add-literal 2)
         (add-literal 0)
         (check-sat)
         (add-literal 3)
         (add-literal -2)
         (add-literal 0)
         (check-sat)
         (add-literal 5)
         (add-literal 4 )
         (add-literal 1)
         (add-literal 0)
         (check-sat)))))

(deftest incremental-2
  (ok
   (loop repeat 10 always
                   (with-sat-solver
                       (mapcar #'add-literal (list 5 0 2 4 0 1 0))
                     (check-sat)
                     (assert (= (length (model)) 6))
                     (mapcar #'add-literal (list 3 7 -8 0 20 0))
                     (check-sat)
                     (assert (= (length (model)) 21))
                     (mapcar #'add-literal (list -2 0 49 50 0))
                     (prog1
                         (check-sat)
                       (assert (= (length (model)) 51)))))))
