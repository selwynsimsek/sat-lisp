#sbcl --eval '(ql:quickload :sat-lisp)' --eval "(sat-lisp::ensure-ipasir-loaded (quote sat-lisp:$1 ))" --eval '(sat-lisp:with-sat-solver (mapcar (quote sat-lisp:add-literal) (list 5 0 2 4 0 1 0))   (when (sat-lisp:check-sat) (print (sat-lisp:model)))(mapcar (quote sat-lisp:add-literal) (list 3 7 -8 0 10 0)) (when (sat-lisp:check-sat) (print (sat-lisp:model)))(mapcar (quote sat-lisp:add-literal) (list  -2 0  49 -50 0)) (when (sat-lisp:check-sat) (print (sat-lisp:model))))' --non-interactive 

sbcl --eval '(ql:quickload :sat-lisp)' --eval '(asdf:test-system :sat-lisp)' --non-interactive
