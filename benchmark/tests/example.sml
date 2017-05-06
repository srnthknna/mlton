
structure Main =
   struct
      fun doit n =
         if n = 0
            then ()
         else let
                val rec fib =
               fn 0 => 0
                | 1 => 1
                | n => fib (n - 1) + fib (n - 2)
                fun fact 0 = 0
                | fact n = n*fact(n-1)
                fun loop ls = let
                            val [a,b,c] = ls
                          in
                            if (a*(~1)) < 0
                            then [a+b,b+a,c+a]
                            else ls
                          end
                fun tupEval ls res = let
                                val tup = loop ls
                                
                                in
                                if (length res) < 3000
                                then tupEval ls (tup::(res))
                                else res
                            end
                 val first = if n mod 2 = 0
				             then loop [10,9,20]
							 else [10,9,20]
                 val ls = tupEval [ 10, 9, 20] []
                 val start = foldl (fn (x,acc) => x + acc) 0 first
                 val res = (List.foldl (fn ([a,b,c],z) => a+b+c+z) start ls)
              in
                 doit (n - 1)
              end
   end
