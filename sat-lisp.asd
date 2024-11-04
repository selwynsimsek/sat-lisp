(defsystem "sat-lisp"
  :version "0.0.1"
  :author "Selwyn Simsek"
  :mailto "selwyn.simsek@cantab.net"
  :license "MIT"
  :depends-on ("cffi"
               "alexandria"
               "metabang-bind")
  :components ((:module "src"
                :components
                ((:file "main"))))
  :description ""
  :in-order-to ((test-op (test-op "sat-lisp/tests"))))

(defsystem "sat-lisp/tests"
  :author "Selwyn Simsek"
  :license "MIT"
  :depends-on ("sat-lisp"
               "rove")
  :components ((:module "tests"
                :components
                ((:file "main"))))
  :description "Test system for sat-lisp"
  :perform (test-op (op c) (symbol-call :rove :run c)))
