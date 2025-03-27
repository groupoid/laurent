%%
%% This is file `cmpart.cls'.
%%
%%
%% Copyright 2007 O.R. Nykyforchyn.
%% Modified by O.R. Nykyforchyn, S.V. Sharyn 2011, 2014, 2015, 2019, 2021
%% All rights reserved.
%%
%% ---------------------------------------------------
%%   This system is distributed in the hope that it will be useful,
%%   but WITHOUT ANY WARRANTY; without even the implied warranty of
%%   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
%%
%% IMPORTANT COPYRIGHT NOTICE:
%%
%% Permission is granted to customize the declarations in this file to
%% serve the needs of your installation.
%%
%% However, NO PERMISSION is granted to distribute a modified version
%% of this file under its original name.
%%
%%
%% MODIFICATION ADVICE:
%%
%% If you want to customize this file, it is best to make a copy of
%% the source file(s) from which it was produced.  Use a different
%% name for your copy(ies) and modify the copy(ies); this will ensure
%% that your modifications do not get overwritten when you install a
%% new release of the standard system.
%%
%% You can then easily distribute your modifications by distributing
%% the modified and renamed copy of the source file.
%%
%%
\ProvidesClass{cmpart}
[2021/02/04 v1.1 style for Carpathian Mathematical Publications]
%
\makeatletter
\def\pj@theoname{Theorem}
\def\pj@proponame{Proposition}
\def\pj@lemmaname{Lemma}
\def\pj@corolname{Corollary}
\def\pj@remarkname{Remark}
\def\pj@defname{Definition}
\def\pj@exampname{Example}
\def\pj@exampsname{Examples}
\def\pj@recname{Received}
\def\pj@revname{Revised}
\def\pj@keywname{Key words and phrases}
\def\pj@unusedbib{Uncited}
%
\DeclareOption{win}{\PassOptionsToPackage{cp1251}{inputenc}}
\DeclareOption{koi}{\PassOptionsToPackage{koi8-u}{inputenc}}
\PassOptionsToPackage{cp1251}{inputenc}
%
\let\ifpj@draft\iffalse
\let\ifpj@othsec\iffalse
\let\ifpj@thmsec\iffalse
%
\DeclareOption{draft}{\let\ifpj@draft\iftrue \PassOptionsToClass{draft}{article}}
\DeclareOption{bysec}{\let\ifpj@othsec\iftrue}
\DeclareOption{thmbysec}{\let\ifpj@thmsec\iftrue \let\ifpj@othsec\iftrue}
%
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}
%
\ProcessOptions
%
\LoadClass[a4paper]{article}
%
% Page parameters
\topmargin=-15mm
\oddsidemargin=0mm
\evensidemargin=0mm
\headsep=0mm
\headheight=0pt
\headsep=6mm
\headheight=12pt
\textheight=682pt
\textwidth=165mm
%
\let\englishhyphenmins\undefined
\usepackage{inputenc}
\usepackage[T2A]{fontenc}
\usepackage{amsmath,amsfonts,amsthm,amssymb,latexsym}
%
\def\th@plain{\slshape}
\theoremstyle{plain}
%
\ifpj@thmsec
\newtheorem{theorem}{\pj@theoname}[section]
\else
\newtheorem{theorem}{\pj@theoname}
\fi
%
\ifpj@othsec
 \newtheorem{proposition}{\pj@proponame}[section]
 \newtheorem{lemma}{\pj@lemmaname}[section]
 \newtheorem{corollary}{\pj@corolname}[section]
 \newtheorem{remark}{\pj@remarkname}[section]
 \newtheorem{definition}{\pj@defname}[section]
 \newtheorem{example}{\pj@exampname}[section]
 \newtheorem{examples}[example]{\pj@exampsname}
\else
 \newtheorem{proposition}{\pj@proponame}
 \newtheorem{lemma}{\pj@lemmaname}
 \newtheorem{corollary}{\pj@corolname}
 \newtheorem{remark}{\pj@remarkname}
 \newtheorem{definition}{\pj@defname}
 \newtheorem{example}{\pj@exampname}
 \newtheorem{examples}[example]{\pj@exampsname}
\fi
%
\newtheorem*{theorem*}{\pj@theoname}
\newtheorem*{proposition*}{\pj@proponame}
\newtheorem*{lemma*}{\pj@lemmaname}
\newtheorem*{corollary*}{\pj@corolname}
\newtheorem*{remark*}{\pj@remarkname}
\newtheorem*{definition*}{\pj@defname}
\newtheorem*{example*}{\pj@exampname}
\newtheorem*{examples*}{\pj@exampsname}
%
\let\pj@shorttitle\empty
\newcommand\shorttitle[1]{%
  \gdef\pj@shorttitle{#1}}
%
\let\pj@addresses\empty
\newcommand\institute[1]{%
  \ifx\pj@addresses\empty
      \gdef\pj@addresses{#1}%
  \else
      \g@addto@macro\pj@addresses{\par\vskip 0.1in \noindent #1.}%
  \fi}
%
\let\@email\empty
\newcommand\email[1]{%
  \gdef\@email{\hfil e-mail:\ {\itshape #1} \hfil}}
%
\let\pj@UDC\empty
\newcommand\UDC[1]{%
  \gdef\pj@UDC{#1}}
%
\let\pj@subjclass\empty
\newcommand\subjclass[1]{%
  \gdef\pj@subjclass{#1}}
%
\let\pj@thanks\empty
\renewcommand\thanks{}
\long\def\thanks#1{%
  \gdef\pj@thanks{#1}}
%
\let\pj@received\empty
\newcommand\received[1]{%
  \gdef\pj@received{#1}}
%
\let\pj@revised\empty
\newcommand\revised[1]{%
  \gdef\pj@revised{#1}}
%
\newcommand\enabstract{}
\newcommand\uaabstract{}
%
\let\pj@enauthtitle\empty
\let\pj@enabstract\empty
%
\long\def\enabstract#1#2#3#4{
  \gdef\pj@enauthtitle{#1 {\it #2}}%
  \global\long\def\pj@enabstract{#3}%
  \gdef\pj@enkeywords{#4}
}
%
\let\pj@uaauthtitle\empty
\let\pj@uaabstract\empty
%
\long\def\uaabstract#1#2#3#4{
  \gdef\pj@uaauthtitle{#1 {\it #2}}%
  \global\long\def\pj@uaabstract{#3}%
  \gdef\pj@uakeywords{#4}
}
%
\AtBeginDocument{%
    \let\shorttitle\undefined
    \let\UDC\undefined
    \let\subjclass\undefined
    \let\received\undefined
    \let\revised\undefined
    \renewcommand{\refname}{References}
}
%
\long\def\maketitle{%
    \ifpj@draft
       \ifx\@author\empty  \def\@author{\textbf{Maksym Sokhatskyi}}\fi
       \ifx\@title\empty  \def\@title{\textbf{Laurent Proof Assistant}}\fi
       \ifx\pj@UDC\empty  \def\pj@UDC{\textbf{???}}\fi
       \ifx\pj@subjclass\empty  \def\pj@subjclass{\textbf{dfat}}\fi
       \ifx\pj@received\empty  \def\pj@received{\textbf{sadfasdfasdf}}\fi
       \ifx\pj@enauthtitle\empty
         \def\pj@enauthtitle{\@author. {\it \@title}}%
         \def\pj@enabstract{This paper \dots}%
       \fi
       \ifx\pj@uaauthtitle\empty
         \def\pj@uaauthtitle{\@author. {\it \@title}}%
         \def\pj@uaabstract{Стаття \dots}%
       \fi
    \fi
    \ifx\pj@shorttitle\empty  \let\pj@shorttitle\@title \fi
     \@xp\gdef\@xp\pj@firstpage\@xp{\the\c@page}%
    \markboth{{\@author}}{{\pj@shorttitle}}%
    \footnotetext{\textup{\scriptsize{\CYRU\CYRD\CYRK\ \pj@UDC}}}
    \ifx\pj@subjclass\empty \else
       \footnotetext{\textrm{2010 \textit{Mathematics Subject
           Classification:\/}\,\pj@subjclass.}}
    \fi
    \centerline{\sffamily
             \bfseries A manuscript submitted to Carpathian Mathematical Publications}
\vskip0.5em
%
     \hbox to \textwidth {\scriptsize\sffamily  ISSN 2075-9827\qquad e-ISSN 2313-0210\hfill
     \ttfamily https://journals.pnu.edu.ua/index.php/cmp
             }
%
    \vspace{0.3in}
    \ifx\pj@subjclass\empty \else
    \fi
%
    \ifx\pj@thanks\empty \else
       \footnotetext{\textrm{\pj@thanks}}
    \fi
%
    \ifx\@title\empty \else
        \let\@tempa\@title
        \begin{center} 
          \renewcommand{\baselinestretch}{1.3}%
          \textbf{\Large\@tempa} 
        \end{center}%
    \fi
%    
    \ifx\@author\empty \else
        \begin{center} 
          \textbf {\@author} 
        \end{center}%
    \fi
%% English abstract
    {
        \footnotesize
        \vspace{-.5em}
        \quotation
        \ifx\pj@enauthtitle\empty \else
           \par%
           \pj@enabstract
           \par%
           {\itshape \pj@keywname:\/}\; \pj@enkeywords.\\
           \vrule height 0.5truept width 0.15\hsize
           \pj@printaddress
        \fi
        \endquotation
     }
     \vskip40pt
} % end of \maketitle
%
\def\pj@printabstracts{
    \vspace{10pt plus 0.5pt}
    \centerline{\hfill\vrule height 1truept width 0.25\hsize\relax\hfill}
    \vspace{10pt plus 0.5pt} {
        \footnotesize
        \vspace{-.5em}\vspace{0pt}
        \quotation
         \ifx\pj@uaauthtitle\empty \else
           \par\bigskip
           \noindent \pj@uaauthtitle\ {/\kern-2pt/ }
             Привіт
           \par\vspace{3pt}%
           \pj@uaabstract
         \fi
        \endquotation
     }
     \vskip15pt
}
%
\pagestyle{myheadings}
\renewcommand{\@biblabel}[1]{#1.\hfill}
%
\renewcommand{\section}{\@startsection{section}{1}{0pt}{3.5ex plus
    1ex minus .2ex}{2.3ex plus .2ex}{\large\bfseries}}
%
\renewcommand{\subsection}{\@startsection{subsection}{1}{0pt}{1.5ex plus
    1ex minus .2ex}{1ex plus 1ex minus .2ex}{\bfseries}}
%
\renewcommand{\@evenhead}{\footnotesize
    \ifnum\c@page=\pj@firstpage \else \thepage \hfil \textsc {\leftmark}\fi \hfil}
%
\renewcommand{\@oddhead}{\footnotesize
    \hfil\ifnum\c@page=\pj@firstpage \else \textsc {\rightmark}\hfil  \thepage \fi}
%
\newcommand{\logo}{\baselineskip2pc \hbox to\hsize{\hfil\copyright\,\footnotesize
    \@author}}%, \pj@year}}
%
\renewcommand{\footnoterule}{\vspace*{-3pt}
    \hrule width 2cm \vspace*{2.6pt}}
%
\renewcommand{\@oddfoot}{{\ifnum\c@page=\pj@firstpage
    \logo \fi}}
\renewcommand{\@evenfoot}{{\ifnum\c@page=\pj@firstpage
    \logo \fi}}
%
\renewcommand{\@makefntext}[1]{\parindent=1em\noindent  #1}
%
\newcommand\pj@printaddress{%
    \ifx\pj@addresses\empty \else
       \vskip0.2in
       \bgroup
       \footnotesize
       \noindent
       \pj@addresses\\
       \@email
       \egroup
    \fi
}
%
\newcommand\pj@printreceived{%
    \ifx\pj@received\empty \else
       \vskip0.1in
       \bgroup
       \footnotesize
       \itshape
       \noindent
       \hfill \pj@recname~\pj@received
       \ifx\pj@revised\empty \else
       ; \pj@revname~\pj@revised
       \fi
       \egroup
    \fi
}
%
\let\pj@thebibliography\thebibliography
\def\thebibliography{\footnotesize\pj@thebibliography}
%
\AtEndDocument{\pj@printreceived\pj@printabstracts}
%
% ``Clever'' bibliography
\def\@lbibitem[#1]#2{%
     \@ifundefined{seen-b@#2}%
       {\def\@biblabel##1{[\textbf{\pj@unusedbib: ##1}]}}%
       {\def\@biblabel##1{[##1]}}%
     \item[\@biblabel{#1}\hfill]%
     \if@filesw
      {\let\protect\noexpand
       \immediate
       \write\@auxout{\string\bibcite{#2}{#1}}}%
     \fi\ignorespaces}
\def\@bibitem#1{%
     \@ifundefined{seen-b@#1}%
       {\def\@biblabel##1{[\textbf{\pj@unusedbib: ##1}]}}%
       {\def\@biblabel##1{[##1]}}%
     \item\if@filesw \immediate\write\@auxout
       {\string\bibcite{#1}{\the\value{\@listctr}}}\fi\ignorespaces}
\def\@citex[#1]#2{\leavevmode
  \let\@citea\@empty
  \@cite{\@for\@citeb:=#2\do
    {\@citea\def\@citea{,\penalty\@m\ }%
     \edef\@citeb{\expandafter\@firstofone\@citeb\@empty}%
     \if@filesw\immediate\write\@auxout{\string\citation{\@citeb}}\fi
     \@xp\global\@xp\def\csname seen-b@\@citeb\endcsname{seen}%
     \@ifundefined{b@\@citeb}{\hbox{\reset@font\bfseries ?}%
       \G@refundefinedtrue
       \@latex@warning
         {Citation `\@citeb' on page \thepage \space undefined}}%
       {\@cite@ofmt{\csname b@\@citeb\endcsname}}}}{#1}}
%% End of file `cmpart.cls'.