## Goal

Given a Haskell expression as an AST, evaluate it step-by-step, showing 
each step (e.g. pattern matching, function application) to the user. 
Intended to be useful as an educational and perhaps debugging tool.

## Project post-mortem

I largely stopped working on stepeval some years ago. It turned out to 
be harder than I expected, and I eventually grew exasperated with the 
mediocre, buggy results. I still think the goal is a good goal, but I 
haven't yet returned to it with the lessons I learned to see if I could 
make a better attempt at it.

At the time I first started writing it, I had never written a compiler 
or interpreter before, and that lack of experience was probably costly – 
I set myself too many problems to solve at once. Someone with a better 
background in that department and possibly with the formal education I 
was (am) lacking would probably have a better shot at it, even if they 
took essentially the same approach.

Something I would have looked into before starting this again would be 
using a typed AST, rather than manipulating `Exp` too freely – there are 
seemingly just too many functions `Exp → Exp` for me to write the 
correct one! Evaluation, after all, should be type-preserving, so it 
would seem wasteful to forget that information. Stepeval as it exists 
today had no access to type information, but would have needed it anyway 
if it were to get support for type classes.

Another useful invariant is preservation of normal form, although that's 
perhaps a bit vacuous (and anyway, it would be nice to support stepping 
through expressions that don't have a normal form, like infinite lists).

With the typed angle in mind, my next project after stepeval was an 
step-by-step explainer of type inference, which could conceivably fall 
in scope as part of the same project. You could imagine a first pass 
which annotated everything with its type, and then a second part which 
evaluated the resulting expression. I didn't get much of anywhere with 
that project, anyway.

If I were to come back to this project, I'd probably scale the ambition 
back a bit and instead write a step-by-step evaluator for a small 
sublanguage of Haskell, say let + lambda + case. Indeed, I think that 
was my original intention, but then I decided to get haskell-src-exts to 
do my parsing for me and then I got carried away a bit.

Anyway, it would be good to get a minimal language with its stepper in 
place, because I think a major so-far-undiscussed challenge is coming up 
with a useful and intuitive UI for the whole thing. Just repeatedly 
dumping the entire AST can stop being helpful if you're evaluating some 
tiny subcomponent of a large, complex expression. I had a few different 
ideas for dealing with that, again varying in ambition. The most 
ambitious would be some kind of graphical (probably web) UI where you 
can click on any subexpression to reduce it one step, choosing whatever 
reduction order you liked (or asking the computer to show you what it 
would do next). Less ambitious would just be perhaps taking 
subexpressions out into let bindings and evaluating them outside of 
their context, but it's hard to know what heuristic to use for when to 
do that. Least ambitious would be, don't do anything clever and just 
live with the clumsiness :)

Let me know if you produce something interesting based on any of these 
ideas, or your own similar ones!

## About this implementation

stepeval comes bundled with an executable that can operate as a
command-line utility or a CGI script. In either case it takes an
expression input as a string and displays each step of its evaluation,
until it reaches weak head normal form or, in the case of the CGI
script, a time limit expires.

Note many features of Haskell are unsupported and three of the tests 
fail, one quite basic! I recommend against relying on the accuracy of 
the results of this program.

If you want to see things in action without downloading anything, try
http://bm380.user.srcf.net/cgi-bin/stepeval.cgi
where an example instance of the CGI script is (maybe) running.

## Contact

haskell at benmachine dot co dot uk

or via IRC: benmachine on Freenode or QuakeNet

## Build notes

The version constraints are conservative - only things that I've personally
tested with. If you are told your version of whatever doesn't fit into them,
relax them; if it works, tell me!

## TODO

Rewrite from scratch, after having read the literature about how to
evaluate functional languages properly. Perhaps leaving it in syntax
form is basically unsatisfactory, and the first thing I should do is a
visualisation of the program's graph.

I need to think about how function application is done. Problem is we can't
easily show how guards are stepped through etc. because we can't modify the
original definition. Perhaps we introduce the funbind to a local let binding
and then modify that.

The testsuite has no means for requiring that evaluation stop at a given
point.

In function application, results aren't always shared as much as they should
be. Basically evaluation is often non-strict instead of lazy, as in the
classic example let double x = x + x in double (double 10)

Better support for primitive operations like arithmetic. This may be related
to class instance resolution.

EnumFrom syntax is not at all supported

Type inference would be nice, to resolve class instances.

It would be nice to have a UI in which one could easily change either the
expression to be stepped or the environment it is being stepped in.

Everywhere in the program I have emphasised correctness and simplicity of
code over performance. In a lot of small ways and a few big ones the
efficiency of the algorithms involved is much poorer than it needs to be.

## FIXME

Nested let-scopes aren't properly supported.

If you use an external definitions file, the evaluator doesn't know that
those definitions can't be changed, so pattern bindings that require
evaluation may go wrong. This isn't really a big deal though because such
files are intended mainly for functions, which don't have this problem.

