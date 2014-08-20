(** 

%
\chapter{Introduction}
\label{ch:intro}
%

 *)

(* begin hide *)
Module Intro.
(* end hide *)

(** remove printing ~ *)
(** printing ~ %\textasciitilde% *)
(** printing R $R$ *)
(** printing done %\texttt{\emph{done}}% *)
(** printing congr %\texttt{\emph{congr}}% *)
(** printing of %\texttt{\emph{of}}% *)
(** printing first %\texttt{{first}}% *)
(** printing last %\texttt{\emph{last}}% *)
(** printing suff %\texttt{\emph{suff}}% *)
(** printing have %\texttt{\emph{have}}% *)
(** printing View %\texttt{\emph{View}}% *)
(** printing >-> %\texttt{>->}% *)
(** printing LoadPath %\texttt{\emph{LoadPath}}% *)
(** printing exists %\texttt{{exists}}% *)
(** printing :-> %\texttt{:->}% *)
(** printing <-- $\mathtt{<--}$ *)
(** printing vfun %\texttt{\emph{vfun}}% *)
(** printing do %\texttt{{do}}% *)
(** printing putStrLn %\texttt{\emph{putStrLn}}% *)
(** printing getChar %\texttt{\emph{getChar}}% *)
(** printing heval %\textsf{\emph{heval}}% *)

(**

These lecture notes came out of the author's personal experience of
learning how to structure mechanized reasoning using the Coq proof
assistant and employ Coq in large-scale research projects. The
resulting manuscript offers a brief and comprehensive introduction to
the basic concepts of interactive theorem proving.

The primary audience of this text are the readers with expertise in
software development and programming and knowledge of discrete
mathematic disciplines on the level of an undergraduate university
program. The high-level goal of the course is, therefore, to
demonstrate how much the rigorous mathematical reasoning and
development of robust and intellectually manageable programs have in
common, and how understanding of common programming language concepts
provides a solid background for building mathematical abstractions and
proving theorems formally. The low-level goal of this course is to
provide an overview of the Coq proof assistant, taken in its both
incarnations: as an expressive functional programming language with
dependent types and as a proof assistant providing support for
mechanized interactive theorem proving.

By aiming these these two goals, this manuscript is, thus, intended to
provide a demonstration how the concepts familiar from the mainstream
programming languages and serving as parts of good programming
practices can provide illuminating insights about the nature of
reasoning in Coq's logical foundations and make it possible to reduce
the burden of mechanical theorem proving. These insights will
eventually give the reader a freedom to focus solely on the
_essential_ part of her formal development instead of fighting with a
proof assistant in futile attempts to encode the "obvious"
mathematical intuition---a reason that made many of the new-comers
abandon their attempts to apply the machine-assisted approach for
formal reasoning as an everyday practice.

* Why yet another course on Coq?

The Coq proof assistant%~\cite{Coq-manual}% has been in development
since 1983, and by now there is a number of courses that provide
excellent introductions into Coq-powered interactive theorem proving
and software development. Among the other publicly available
manuscripts, the author finds the following three to be the most
suitable for teaching purposes.

- The classical book _Interactive Theorem Proving and Program
  Development. Coq'Art: The Calculus of Inductive Constructions_ by
  Yves Bertot and Pierre %Cast\'{e}ran~\cite{Bertot-Casteran:BOOK}% is
  a great and exhaustive overview of Coq as a formal system and a
  tool, covering both logical foundations, reasoning methodologies,
  automation tools and offering large number of examples and exercises
  (from which this course borrows some).

- Benjamin Pierce et al.'s _Software Foundations_ electronic
  book%~\cite{Pierce-al:SF}% introduces Coq development from an angle
  of the basic research in programming languages, focusing primarily
  on formalization of program language semantics and type systems,
  which serve both as main motivating examples of Coq usage and a
  source of intuition for explaining Coq's logical foundations.

- The most recently published book, _Certified Programming with
  Dependent Types_ by Adam Chlipala%~\cite{Chlipala:BOOK}% provides a
  gentle introduction to Coq from the perspective of writing programs
  that manipulate _certificates_, i.e., first-class proofs of the
  program's correctness. The idea of certified programming is a
  natural fit for a programming language with dependent types, which
  Coq offers, and the book is structured as a series of examples that
  make the dependently-typed aspect of Coq shine, along with the
  intuition behind these examples and a detailed overview of
  state-of-the-art _proof automation_ techniques.

Although all the three books have been used in numerous introductory
courses for Coq with a large success, it is the author's opinion that
there are still some topics essential for grasping the intuition
behind rigorous and boilerplate-free mathematical reasoning via a
proof assistant that are left underrepresented. This course is
targeted to fill these gaps, while giving the reader enough background
to proceed as a Coq hacker on her own. In particular, this manuscript
describes in detail the following aspects of proof engineering, most
of which are enabled or empowered by Gonthier et al.'s _small-scale
reflection_ extension (SSReflect) to Coq%~\cite{Gontier-al:TR}%:

- Special treatment is given to the _computational_ nature of
  inductive reasoning about _decidable_ propositions, which makes it
  possible to compute a result of the vast majority of them (as
  opposed to prove them constructively) as a boolean value, given that
  they are formulated as computable recursive Coq functions, rather
  than inductive predicates (which is more in the spirit of the
  traditional Coq school).

- Instead of supplying the reader with a large vocabulary of tactics
  necessary for everyday Coq hacking, this course focuses on a _very
  small_ but powerful and _complete_ set of proof constructing
  primitives (of about a dozen in total), offered by SSReflect or
  inherited from the vanilla Coq with notable enhancements.

- This course advocates inductive types' _parameters_ as an
  alternative to _indices_ as a way of reasoning about explicit
  equalities in datatypes with constraints.

- The reasoning by rewriting is first presented from the perspective
  of Coq's definition of the propositional equality and followed by
  elaboration on the idea of using _datatype indices_ as a tool to
  define client-specific conditional _rewriting rules_.

- These manuscript explains the essentials of SSReflect's _boolean
  reflection_ between the sort [Prop] and the datatype [bool] as a
  particular case of conditional rewriting, following the spirit of
  the computational approach to the proofs of decidable propositions.

- Formal encoding of familiar mathematical structures (e.g., monoids
  and lattices) is presented by means of Coq's _dependent records_ and
  overloading mathematical operations using the mechanism of
  _canonical instances_.

- A novel (from a teaching perspective) case study is considered,
  introducing the readers to the concepts of Hoare Type Theory and
  describing the basics of type-based reasoning about _imperative
  programs_ by means of _shallow embedding_.

** What this course is about

Besides the enumerated above list of topics, which are described in
detail and supported by a number of examples, this course supplies
some amount of "standard" material required to introduce a reader with
a background in programming and classical mathematical disciplines to
proof engineering and program development in Coq. It starts from
explaining how simple functional programs and datatypes can be defined
and executed in the programming environment of Coq, proceeding to the
definition of propositional logic connectives and elements of
interactive proof construction. Building further on the programming
intuitions about algebraic datatypes, this manuscript introduces a
definition of the propositional equality and the way to encode custom
rewriting rules, which then culminates with a discussion on the
boolean reflection and reasoning by means of computation. This
discussion is continued by revising important principles of proofs by
induction in Coq and providing pointers to the standard SSReflect
libraries, which should be used as a main component for everyday
mathematical reasoning. The course concludes by reconciling all of the
described concepts and Coq/SSReflect reasoning principles by tacking a
large case study---verifying imperative programs within the framework
of Nanevski et al.'s Hoare Type
Theory%~\cite{Nanevski-al:ICFP06,Nanevski-al:JFP08}%.

** What this course is not about

There is a range of topics that this course does not cover, although
it is the author's belief that the provided material should be
sufficient for the reader to proceed to these more advanced subjects
on her own. Some of the exciting topics, which are certainly worth
studying but lie beyond the scope of this manuscript, are listed below
together with pointers to the relevant bibliographic references.

- Reasoning about infinite objects in Coq via of co-induction (see
  Chapters 5 and 7 of the book%~\cite{Chlipala:BOOK}% as well as the
  research papers%~\cite{Hur-al:POPL13,Leroy-Grall:IC09}%).

- Proof automation by means of tactic engineering (see%~\cite[Chapters
  13--15]{Chlipala:BOOK}% and the
  papers%~\cite{Ziliani-al:ICFP13,Stampoulis-Shao:ICFP10,Stampoulis-Shao:POPL12}%)
  or lemma overloading%~\cite{Gontier-al:ICFP11}%.

- Using a proof assistant in the verification of program
  calculi%~\cite{Pierce-al:SF,Aydemir-al:POPL08}% and optimizing
  compilers%~\cite{Appel:BOOK14}% as well as employing Coq to specify
  and verify low-level and concurrent
  programs%~\cite{Nanevski-al:ESOP14,Chlipala:PLDI11,Feng-al:PLDI06,Cai-al:PLDI07}%.

** Why SSReflect?

%\index{SSReflect|textbf}%

A significant part of this course's material is presented using the
SSReflect extension of Coq%~\cite{Gontier-al:TR}%, developed as a part
of the Mathematical Components
project%\footnote{\url{http://www.msr-inria.fr/projects/mathematical-components-2/}}%
in order to facilitate the automated reasoning in very large
mathematical developments, in particular, the fully formal
machine-checked proofs of the %\emph{four color
theorem}~\cite{Gonthier:AMS08}% and %\emph{Feit-Thompson (odd order)
theorem}~\cite{Gonthier-al:ITP13}%.

%\index{four color theorem}%
%\index{odd order theorem|see {Feit-Thompson theorem}}%
%\index{Feit-Thompson theorem}%

SSReflect includes a small but complete set of novel primitives for
interactive proof construction (tactics), different from the
traditional set provided by Coq. It also comes with a large library of
various algebraic structures, ranging from natural numbers to graphs,
finite sets and algebras, formalized and shipped with exhaustive
toolkits of lemmas and facts about them. Finally, SSReflect introduces
some mild modifications to Coq's native syntax and the semantics of
the proof script interpreter, which makes the produced proofs
significantly more concise.

Using SSReflect for the current development is not the goal by itself:
a large part of the manuscript could be presented using traditional
Coq without any loss in the insights but, perhaps, some loss in
brevity. However, what is more important, using SSReflect's libraries
and tactics makes it much easier to stress the main points of this
course, namely, that (a) the proof construction process should rely on
Coq's native computational machinery as much as possible and (b)
rewriting (in particular, by equality) is one of the most important
proof techniques, which should be mastered and leveraged in the
proofs. Luckily, the way most of the lemmas in SSReflect libraries are
implemented makes them immediately suitable to use for rewritings,
which directly follows the natural mathematical intuition. The
enhancements SSReflect brings over the standard Coq rewriting
machinery also come in handy.

Last, but not least, SSReflect comes with a much improved [Search]
tool (comparing to the standard one of Coq). Given that a fair part of
time spent for development (either programs and proofs) is typically
dedicated to reading and understanding the code (or, at least,
specifications) written by other implementors, the [Search] tool turns
out to be invaluable when it comes to looking for necessary
third-party facts to employ in one's own implementation.

In the further chapters of this course, we will not be making
distinction between native Coq and SSReflect-introduced commands,
tactics and tacticals, and will keep the combined lists of them in the
Index section at the end of the manuscript.

* Prerequisites

The reader is expected to have some experience with mainstream
object-oriented and functional programming languages, such as
Scala%~\cite{Scala-spec}%, Haskell%~\cite{Haskell-report}%,
OCaml%~\cite{Ocaml-spec}% or Standard ML%~\cite{SML-report}%. While
strong knowledge of any of the mentioned languages is not mandatory,
it might be useful, as many of the Coq's concepts making appearance in
the course are explained using the analogies with constructs adopted
in practical programming, such as algebraic datatypes, higher-order
functions, records and monads.

While this manuscript is aiming to be self-contained in its
presentation of a subset of Coq, it would be %\naive~%to expect it to
be the _only_ Coq reference used for setting-up a formal
development. That said, we encourage the reader to use the standard
Coq manual%~\cite{Coq-manual}% as well as SSReflect
documentation%~\cite{Gontier-al:TR}% whenever a unknown tactic, piece
of syntax or obscure notation is encountered. Coq's [Search],
%\texttt{Locate}% and [Print] tools, explained in
%Chapter~\ref{ch:funprog}% are usually of great help when it comes to
investigating what someone's Coq code does, so don't hesitate to use
them.

Finally, we assume that the Emacs text editor %\index{Emacs}% with a
Proof General mode installed %\index{Proof General}% (as explained
further in this chapter) will be used as the environment for writing
code scripts, and the GNU %\texttt{make}% machinery is available at
the reader's machine in order to build the necessary libraries and
tools.

* Setup

In order to be able to follow the manuscript and execute the examples
provided, the reader is expected to have Coq with SSReflect installed
at her machine. This section contains some general instructions on the
installation and set-up. Most of the mentioned below binaries can be
downloaded from the following URL, accompanying these notes:

%
\begin{center}
\url{http://ilyasergey.net/pnp}
\end{center}
%

** Installing Coq and SSReflect
%\label{sec:install-coq}%

The sources of this manuscript have been compiled and tested with Coq
version 8.4 and SSReflect version 1.4. It is not guaranteed that the
same examples will work seamlessly with different versions. Therefore,
several recipes on how to build install the necessary software are
provided below.

- Windows users are encouraged to use Pierre-Yves Strub's installer
  with the Coq bundle,%\footnote{Available from
  \url{http://pierre-yves.strub.nu/}.}% which already contains all the
  necessary components including Coq v8.4pl2, SSReflect v1.4 and Emacs
  with Proof General installed.

- Linux and Mac OS X users can compile Coq 8.4 and SSReflect from
  sources, which would take around two hours of their
  time.%\footnote{Getting Coq 8.4 using a system-specific package
  manager, such as \emph{aptitude} or \emph{MacPorts} is another option,
  although the Coq version acquired this way is not guaranteed to work
  properly with SSReflect 1.4.}%

  In order to be compiled, Coq requires Objective Caml version 3.11.2
  or later, Camlp5, GNU Make version 3.81 or later (see the
  <<INSTALL>> file from the archive with sources for more details on
  configuration and installation). Once compiled, the following
  environment variables should be set (e.g., in <<~/.bashrc>> or
  <<~/.profile>> configuration files) to build SSReflect (with the
  respective paths chosen during the Coq's installation):

<<
    export COQBIN="/usr/local/bin/"
    export COQ_MK="/usr/local/bin/coq_makefile"
>>

  After compiling SSReflect, the file <<bin/ssrcoq>> should be created
  in the <<ssreflect-1.4>> folder. It should be then manually copied
  to the same folder where the Coq binaries are located (e.g.,
  <</usr/local/bin>> in the default case of Unix-like systems). It is
  also recommended to keep SSReflect's sources easily accessible as
  reading them might be helpful when working with libraries (see the
  files in the folder <<ssreflect-1.4/theories/>>). 

  Upon installing SSReflect via %\texttt{make install}%, the following
  environment variable should be also set up:

<<
    export SSRCOQ_LIB="/usr/local/lib/coq/user-contrib/Ssreflect/" 
>>

  Alternatively, instead of running %\texttt{make install}%, one can
  set up the environment variable %\texttt{SSRCOQ\_LIB}% to point to
  the folder %\texttt{ssreflect-location/theories}%, which contains
  all SSReflect modules compiled (and %\texttt{ssreflect-location}%
  denotes the location of the directory where SSReflect has been
  unpacked to).

** Emacs set-up

Emacs%\footnote{\url{http://www.gnu.org/software/emacs/}}% (or
Aquamacs%\footnote{\url{http://aquamacs.org/}}% for Mac OS X users)
text editor provides a convenient environment for Coq development,
thanks to the Proof General mode. After downloading and installing
Emacs, download and install Proof General,%\footnote{Available from
\url{http://proofgeneral.inf.ed.ac.uk/download}.}% following the
instructions below. Upon downloading and unpacking, add the following
lines into the <<.emacs>> configuration file located in the home
directory in Unix and in <<C:\>> root in Windows (possibly replacing
the %\texttt{\textasciitilde/misc/}% part with the path where Proof
General and SSReflect sources were unpacked).

<<
    ;; Proof General support
    (load-file "~/misc/ProofGeneral-4.2/generic/proof-site.el") 

    ;; SSReflect support 
    (load-file "~/misc/ssreflect-1.4/pg-ssr.el")
>>

Linux users, more used to the Windows-style Copy/Paste/Undo keystrokes
can also find it convenient to enable the Cua mode in Emacs, which can
be done by adding the following lines into the %\texttt{.emacs}% file:

<<
    (cua-mode t)
    (setq cua-auto-tabify-rectangles nil)
    (transient-mark-mode 1)
    (setq cua-keep-region-after-copy t) 
>>

Every Coq file has the extension %\texttt{.v}%. Opening any
%\texttt{.v}% file will automatically trigger the Proof General
mode. Once the mode is launched, in the menu <<Proof-General>>, choose
the item: << Advanced -> Customize -> Coq -> Coq Prog Name >> and
change the value of the variable to << ssreflect-location/bin/ssrcoq
>> or << ssreflect-location\bin\ssrcoq >> for Windows/Cygwin users,
where %\texttt{ssreflect-location}% is the location of your SSReflect
directory with compiled binaries (or, alternatively, a parent
catalogue of the %\texttt{bin}% folder containing Coq and SSReflect's
binaries, where %\texttt{ssrcoq}% has been previously copied, as it
was suggested).

** Getting the lecture files and HTT sources
%\label{sec:htt-sources}%

The reader is encouraged to download the additional material for this
course in the form of Coq files with all examples from the manuscript
plus some additional exercises. The archive with these sources is
named
%\href{http://ilyasergey.net/pnp/pnp-lectures.zip}{\texttt{pnp-lectures.zip}}%
and can be downloaded from the
%\href{http://ilyasergey.net/pnp/}{course url}%
given above. The table below describes the correspondence between the
chapters of the manuscript and the accompanying files.

%
\vspace{15pt}
\begin{center}
\begin{tabular}{|c|l|l|}
\hline
\textbf{\textnumero} & \textbf{Chapter title} & \textbf{Coq file} 
\\ \hline
\ref{ch:funprog} & Functional Programming in Coq & \texttt{FunProg.v}
\\ \hline
\ref{ch:logic} & Propositional Logic & \texttt{LogicPrimer.v} 
\\ \hline
\ref{ch:eqrew} & Equality and Rewriting Principles & \texttt{Rewriting.v} 
\\ \hline
\ref{ch:boolrefl} & Views and Boolean Reflection & \texttt{BoolRefl.v} 
\\ \hline
\ref{ch:ssrstyle} & Inductive Reasoning in SSReflect & \texttt{SsrStyle.v} 
\\ \hline
\ref{ch:depstruct} & Encoding Mathematical Structures & \texttt{DepRecords.v} 
\\ \hline
\ref{ch:htt} & Case Study: Program Verification in Hoare Type Theory & \texttt{HTT.v} 
\\ \hline
\end{tabular} 
\end{center}
\vspace{15pt}
%

For the examples of Chapter%~\ref{ch:htt}% and the corresponding
lecture source file, the sources of the Hoare Type Theory development
will be required. The archive
%\href{http://ilyasergey.net/pnp/htt.zip}{\texttt{htt.zip}}%
with sources and the make-script can be downloaded from the
%\href{http://ilyasergey.net/pnp/}{course
url}%. After downloading and unpacking, the sources should be compiled
via the %\texttt{make}% command, given that Coq and SSReflect are
properly installed, as described previously (make sure that the
environment variables %\texttt{COQBIN}% and %\texttt{SSRCOQ\_LIB}%)
are set up properly, as explained in
Section%~\ref{sec:install-coq}%). For the immediate compatibility with
the lecture sources, it is recommended to place the %\texttt{htt}% and
%\texttt{lectures}% folders beneath a common parent folder. After
unzipping the archive with lectures, run the %\texttt{make}% command
from the folder %\texttt{lectures}% (assuming that the HTT sources are
already build and are located in the sibling folder): it should build
all %\texttt{.v}% files in it and serve as a consistency check for
your setup.

Solutions for all of the exercises from the course are available
on demand: drop me a line if you're interested
(%\href{mailto:ilya.sergey@imdea.org}{\texttt{ilya.sergey@imdea.org}}%),
so I will mail you back the archive.

** Using a virtual machine image

If compiling and installing Coq and SSReflect from scratch looks like
too much hassle, there is also a possibility to use a virtual machine
image with all libraries preinstalled (including HTT) and Emacs set up
to work with SSReflect. The image requires Oracle %\index{VirtualBox}%
VirtualBox to be used;%\footnote{Available from
\url{http://www.virtualbox.org/wiki/Downloads}.}% it is about %1.8~GB%
size and can be obtained from the same
%\href{http://ilyasergey.net/pnp/}{course url}%
as other artifacts (look for the file
%\texttt{Ubuntu-CoqSSR-PnP.ova}%). It runs Ubuntu 14.04 and
automatically logs in when started with the user %\texttt{coquser}%
(use the password %\texttt{coquser}% whenever it is required). The
folder %\texttt{\textasciitilde/misc}% contains the sources of
SSReflect and Proof General. HTT sources and this course's lecture
files are located in %\texttt{\textasciitilde/htt}% and
%\texttt{\textasciitilde/lectures}%, correspondingly.

* Naming conventions

Coq as a tool and environment for interactive theorem proving
incorporates a number of entities in itself. As a programming and
specification language, Coq implements a dependently-type _calculus_
(i.e., a small formal programming language) _Gallina_,
%\index{Gallina}% which is an extension of the _Calculus of Inductive
Constructions_ (CIC) explained in Chapter%~\ref{ch:logic}%. Therefore,
all the expressions and programs in Coq, including standard
connectives (e.g., %\texttt{if-then-else}% or %\texttt{let-in}%) are
usually referred to as _Gallina terms_. In the listing, keywords of
Gallina terms will be usually spelled using %\texttt{typewriter
monospace font}%. The defined entities, such as functions, datatypes
theorems and local variables will be usually spelled in the
%\emph{italic}% or %\textsf{sans serif}% fonts.

On top of the language of programs in Coq there is a language of
_commands_ and _tactics_, which help to manage the proof scripts,
define functions and datatypes, and perform queries, such as searching
and printing. The language of Coq commands, such as [Search] and
[Print], is called _Vernacular_. %\index{Vernacular}% Commands and
tactics, similarly to the keywords, are spelled in %\texttt{typewriter
monospace font}%.

In the rest of the manuscript, though, we will be abusing the
terminology and blur the distinction between entities that belong to
Galina, Vernacular or Coq as a framework, and will be referring to
them simply as "Coq terms", "Coq tactics" and "Coq commands".


*)

(* begin hide *)
End Intro.
(* end hide *)
