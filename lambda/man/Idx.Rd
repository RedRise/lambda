\name{Idx}
\alias{Idx}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
iterator going through expanded windows
}
\description{
this iterator will go through every interval of the form [1:i]
}
\usage{
Idx(M, ds = 1, stp = 1, pvt = 1, rsz = TRUE)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{M}{
a [list of [list of...]] array. The data-structure to go through.
}
  \item{ds}{
integer, the dimension to explore.
}
  \item{stp}{
integer, the increment of the sequence.
}
  \item{pvt}{
integer or character, pointing to the 'pivot', i.e. an element that have to appear
in the sequence. When pvt is a character, a match on corresponding dimnames is performed.
If pvt is an integer, the corresponding element is included.
}
  \item{rsz}{
boolean (default=TRUE), relevant only if stp!=1. Should we keep output format
with same size than the input?

}
}
\details{
%%  ~~ If necessary, more details than the description above ~~
}
\value{
\item{expr.l }{a list of expressions or integer vectors corresponding to all the 
rolling windows interval}
\item{glob.sz }{an integer. The size of expr.l }
\item{glob.n }{ dimnames of output. If resizing asked (rsz=TRUE), equals to initial
corresponding dimnames, otherwise dimnames sub-elements }
\item{cast.ix }{If rsz=FALSE then NULL, else an integer vector pointing to 
extracted indices.}
}
\references{
%% ~put references to the literature/web site here ~
}
\author{
EONOS INVESTMENT TECHNOLOGIES
}
\note{
%%  ~~further notes~~
}

%% ~Make other sections like Warning with \section{Warning }{....} ~

\seealso{
The global iterator caller: \code{\link{lambda}}, other iterators:
\code{\link{dx}}, \code{\link{win}}, \code{\link{ap}}
}
\examples{
## Generate a simple matrix with dimnames
x <- matrix( rnorm(20), 5, 4 )
rownames(x) <- paste('row',1:nrow(x),sep='_')
colnames(x) <- paste('col',1:ncol(x),sep='_')

## a column-wise cumulative sum
lambda( sum, x, list(Idx,dx) )

## a row-wise cumulative standard deviation
lambda( sd, x, list(dx, Idx) )

}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
\keyword{ ~kwd1 }
\keyword{ ~kwd2 }% __ONLY ONE__ keyword per line
