(defpackage sat-lisp/tests/main
  (:use :cl
        :sat-lisp
        :rove))
(in-package :sat-lisp/tests/main)

;; NOTE: To run this test file, execute `(asdf:test-system :sat-lisp)' in your Lisp.

(deftest test-target-1
  (testing "should (= 1 1) to be true"
    (ok (= 1 1))))
