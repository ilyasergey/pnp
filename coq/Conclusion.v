(* begin hide *)
Module Conclusion.
(* end hide *)


(**
%
\chapter{Conclusion}
\label{ch:conclusion}

The goal of this course was to introduce a reader with a background in
programming and abstract algebra to interactive theorem proving in the
Coq proof assistant.

Starting from the concepts, familiar from the world of functional
programming, such as higher-order functions, algebraic datatypes and
recursion, we have first considered Coq as a programming language in
\textbf{Chapter~\ref{ch:funprog}}. The programming language intuition
helped us to move further into the realm of propositional logic and
comprehend the way of encoding and proving propositions constructively
in \textbf{Chapter~\ref{ch:logic}}. At that point a number of familiar
logical connectives came in the new light of Curry-Howard
correspondence with respect to the familiar datatypes. Introducing
universal and existential quantification, though, required to appeal
to the dependently-typed part of Coq as a programming language, which moved
us beyond a simple propositional logic, so we could make statements
over arbitrary entities, not just propositions. At the same point we
had the first encounter with Coq's proof construction machinery. To
unleash the full power of the mathematical reasoning, in
\textbf{Chapter~\ref{ch:eqrew}} we learned about the way equality is
defined in Coq and how it is used for proofs by rewriting. In the
process we have learned that equality is just one way to encode a
rewriting principle and seen how custom rewriting principles can be
encoded in Coq. It turned out that one of the most useful rewriting
principles is the ability to ``switch'' in the reasoning between the
constructive and computable formulation of decidable propositions---a
trick that working mathematicians perform on the fly in their
minds. In \textbf{Chapter~\ref{ch:boolrefl}}, we have seen how the
same switch can be implemented seamlessly in Coq using the boolean
reflection machinery.  With the introduction of boolean reflection,
our journey in the world of interactive theorem proving took a path,
paved by Gonthier's et al.'s Ssreflect extension, embracing and
leveraging the computational power of Coq as a programming language to
the extreme. The motto ``let Coq compute a part of the proof for you,
since it's a programming language after all!'', witnessed by
formulation of boolean functions instead of decidable inductive
predicates, has been supplied by a number of examples in
\textbf{Chapter~\ref{ch:ssrstyle}}, in which we have also exercised in
proofs by induction of different flavours. Mathematics is a science of
abstract structures and facts, and formalizing such structures and
facts is an important component of rigorous reasoning. In
\textbf{Chapter~\ref{ch:depstruct}} we have learned how the concepts
of records and type classes, familiar from languages like C and
Haskell, can be directly employed, powered by Coq's dependent types,
to encode a variety of mathematical structures from the course of
abstract algebra. \textbf{Chapter~\ref{ch:htt}} brought all of the
presented programming and proving concepts together and made them
to work in concert to tackle a large case study---specifying and
verifying imperative programs in the framework of Hoare Type Theory.

\section*{Future directions}

I hope that this short and by all means not exhaustive course on
mechanized mathematics in Coq was helpful in reconciling the reader's
programming expertise and mathematical background in one solid
picture. So, what now?

In the author's personal experience, fluency in Coq and the ability to
operate with a large vocabulary of facts, lemmas and tactics is a
volatile skill, which fades out at an alarming rate without regular
practice in proving and mechanized reasoning. On the bright side, this
is also a skill, which can fill one with a feeling of excitement from
a progressive reasoning process and the rewarding sense of achievement
that few human activities bring.

With this respect, it seems natural to advise the reader to pick a
project on her own and put it to the rails of machine-assisted
proving. Sadly, formalizing things just for the sake of formalization
is rarely a pleasant experience, and re-doing someone's results in Coq
just to ``have them in Coq at any price'' is not a glorious goal by
itself. What is less obvious is that setting up mathematical reasoning
in Coq usually brings some \emph{brand new} insights that usually come
from directions no one expected. Such insights might be due to
exploding proofs, which are repetitive and full of boilerplate code
(seems like a refactoring opportunity in someone's math?) or because
of the lack of abstraction in a supposedly abstract concept, which
overwhelms its clients with proof obligations, once being applied to
something its designer mathematician didn't foresee (a case of leaky
abstraction?). Coq combines programming and mathematics in a single
framework. I believe, this must be the point, at which several decades
of mastering the humanity's programming expertise should pay back and
start being useful for producing the genuine \emph{understanding} of
formally stated facts and proofs about them. 


% *)

(* begin hide *)
End Conclusion.
(* end hide *)
