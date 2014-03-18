#lang pyret/check

# cfwae.arr - Template of a simple interpreter for CFWAE
# Copyright (C) 2014 - Humberto Ortiz-Zuazaga <humberto.ortiz@upr.edu>

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
                                                                       
#Name: Luis A. Albertorio
#Email: luisalbertorio21@gmail.com

key_words=["+", "-", "*", "/", "with", "fun", "if0"]

# Bindings map identifiers to values
data Binding:
  | bind (name :: String, expr :: CFWAE)
end

# An Environment is a List<Env>
data Env:
  | env (name :: String, value :: CFWAE-Value)
end

# An Environment is a List<Binding>
mt-env = []
xtnd-env = link

# Data type for expressions
                          
data CFWAE:
  | numC (n :: Number)
  | binopC (op :: String, l :: CFWAE, r :: CFWAE)
  | withC (bindings :: List<Binding>, expr :: CFWAE)
  | idC (name :: String)
  | if0C (test-expr :: CFWAE, then-expr :: CFWAE, else-expr :: CFWAE)
  | fdC (args :: List<String>, body :: CFWAE)
  | appC (f :: CFWAE, args :: List<CFWAE>)
end

# and values
data CFWAE-Value:
  | numV (n :: Number)
  | closV (f :: CFWAE, e :: List<Binding>) # ExprC must be an fdC
end

fun look(foo :: List, fighter::List<String>) -> List<Binding>:
doc:"Checks identifier, if its in key_word list raises error, if not puts it in list"
  cases (List) foo:
  | empty => empty
  | link(op,args) => if fighter.member(op):
                        raise("already in list")
                     else:
                       link(bind(list.index(op, 0), parse(list.index(op, 1))), look(args, link(list.index(op, 0), fighter)))
          end
     end
end

fun parse-formals(args :: List<String>, cf :: List<String>) -> List<String>:
doc:"Does the same as look but for 'fun'"
     cases (List) args:
       | empty => empty
       | link(f,r) => if cf.member(f):
                              raise("identifier already in the List")
                      else:
                              link(f, parse-formals(r,link(f,cf)))
              end
       end
end

fun createlistforappc(lista :: List) -> List<CFWAE>:
doc:"parse all arguments that we are passin for appC recursively"
 cases(List) lista:
  | empty => empty
  | link(f, r) => link(parse(f) , createlistforappc(r))
 end
end

fun parse(s) -> CFWAE:
  doc: "Parse reads an s-expression S and returns the abstract syntax tree."

  if Number(s):
      numC(s)
  else if String(s):
      if key_words.member(s):
          raise("cant use keywords")
      else:
         idC(s)
      end
  else if List(s):
      cases (List) s:
      |empty => raise("parse: empty list")
      |link(op,args) => 
           argL = list.index(args, 0)
           argR = list.index(args, 1)
    if args.length()==1:

           raise("list too short")

    else if op == "if0":

           argIf = argL
           argThen = argR
           argElse= list.index(args, 2)
           if0C(parse(argIf), parse(argThen), parse(argElse))

    else if ((op == "+") or (op == "-") or (op == "*") or (op == "/")) and (args.length()==2): 
            
            binopC(op, parse(argL),parse(argR))
     
    else if op == "with":
      
            withC(look(argL, key_words), parse(argR))
         
    else if op == "fun":
         
            fdC(parse-formals(argL, key_words), parse(argR))
    else:

            appC(parse(op), createlistforappc(args))

   end
  end
 end
where:
  parse([]) raises("parse")
  parse(read-sexpr("(+ 5)")) raises("list too short")
  parse(read-sexpr("3")) is numC(3)
  parse(read-sexpr("(if0 0 1 2)")) is if0C(numC(0), numC(1), numC(2))
  parse(read-sexpr("(fun (x) x)")) is fdC(["x"], idC("x"))
  parse(read-sexpr("(fun (x x) x)")) raises "i"
  parse("l") is idC("l")
  parse(["with", [["x", 2],["y", 4]], ["if0", 1, 1, 2]]) is withC([bind("x", numC(2)), bind("y", numC(4))], if0C(numC(1), numC(1), numC(2)))
  parse(["with", [["x", 2],["y",4]], ["+", 3, 2]]) is withC([bind("x", numC(2)), bind("y", numC(4))], binopC("+", numC(3), numC(2)))
  parse(read-sexpr("((fun (x) (+ x x)) 7 4)")) is appC(fdC(["x"], binopC("+", idC("x"), idC("x"))), [numC(7), numC(4)])
end

#helper functions
fun plus-v(v1, v2): numV(v1.n + v2.n) end
fun mult-v(v1, v2): numV(v1.n * v2.n) end
fun div-v (v1, v2): numV(v1.n / v2.n) end
fun minus-v(v1, v2): numV(v1.n - v2.n) end

fun lookup(s:: String, nv::List<Env>) -> CFWAE-Value:
doc:"checks string to evaluate expression in list"
  cases (List) nv:
  | empty => raise("Unbound identifier")
  | link(first, rest) => if s == first.name:
                           first.value
                        else:
                           lookup(s,rest)
                     end
            end
where:
 #test for lookup
 lookup("nirvana", mt-env) raises "U"
 lookup("x", [env("x", numV(2))]) is numV(2)
 lookup("y", [env("x", numV(2))]) raises("Unbound identifier")
 lookup("y", [env("x", numV(2)), env("y", numV(3))]) is numV(3)

end

fun interpV(w:: CFWAE):
 doc:"Helper interp with enviorments so we can perform withC, fdC and idC"
 envi = []
 interp(w, envi)
end

fun envy(a::List<String>, args::List<CFWAE> ,oldenv::List<env>):
doc:"helper function for the appC, links oldenv with new one"
 if args.length() <> a.length():
    raise("error")
else:
cases (List<CFWAE>) args:
    |empty => oldenv
    |link(f,r) =>
          cases (List<String>) a:
             |empty => empty
             |link(q,w) => 
               newList = envy(r, w, oldenv)
               link(env(q, interp(f, oldenv)),  newList)
   end
  end
 end
end

fun interp(e :: CFWAE, mv::List<Env>) -> CFWAE-Value:
  doc: "Execute the expression E, return the result of evaluation."
  cases(CFWAE) e:
      | numC(n) => numV(n)
      | binopC(op,L,R)=> 
         if op == "+":
               plus-v(interp(L, mv),interp(R,mv))
          else if op == "-":
               minus-v(interp(L, mv),interp(R,mv))
          else if op == "*":
               mult-v(interp(L, mv),interp(R,mv))         
          else if op == "/":
             if R == 0:
                raise("Division by zero")
             else:
               div-v(interp(L, mv), interp(R, mv))
          end    
         else: raise("U")
      end
      | if0C(i, th, els) => 
            if interp(i, mv) == numV(0):
               interp(th, mv)
            else:
               interp(els, mv)
            end
   
     | withC(binds, expr) => 
          new-env = for map(b from binds):
              env(b.name, interp(b.expr, mv))
           end
              interp(expr, new-env.append(mv))

     |fdC(_,_) => closV(e,mv)

     |idC(n) => lookup(n, mv)

     |appC(q,w) => orita= interp(q,w)
                   newenv = envy(orita.f.args, w, mv)
                   interp(orita.f.body, newenv) 
          
    end
where:
  #test for if0
  interpV(if0C(numC(0), numC(1), numC(2))) is numV(1)
  interpV(if0C(numC(1), numC(3), numC(2))) is numV(2)

  #test for binopC
  interpV(binopC("+",numC(5),numC(5))) is numV(10)
  interpV(binopC("-", numC(3), numC(2))) is numV(1)
  interpV(binopC("*", numC(5), numC(5))) is numV(25)
  interpV(binopC("/", numC(10), numC(2))) is numV(5)
  interpV(binopC("/", numC(2), numC(0)))raises("Division by zero")
  interpV(binopC("#", numC(0), numC(2)))raises("U")
  interpV(binopC("-",numC(0),numC(10))) is numV(-10)

  #test for withC
  interpV(withC([bind("a", numC(1)), bind("b", numC(4))], binopC("+", idC("a"), numC(6)))) is numV(7)

  #test for appC
  interpV(appC(fdC(["x"], binopC("+", idC("x"), idC("x"))), [numC(7)])) is numV(14)
  interpV(appC(fdC(["x"], idC("x")), [numC(1)])) is numV(1)

  #test for fdC
  interpV(fdC(["d"], idC("d"))) is closV(fdC(["d"], idC("d")), [])
end

check:
  fun run(s): interpV(parse(read-sexpr(s))) end
  run("(if0 0 1 2)") is numV(1)
  run("(if0 1 2 3)") is numV(3)
  run("(/ 2 1)") is numV(2)
  run("(+ 7 3)") is numV(10)
  run("-5") is numV(-5)
  run("(* 6 6)") is numV(36)
  run("(with ((x 2) (y 4)) (if0 1 x y))") is numV(4)
  run("(with ((x 2) (y 4)) (if0 0 x y))") is numV(2)
end
