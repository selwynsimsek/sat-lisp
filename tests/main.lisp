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
