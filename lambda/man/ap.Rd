\name{ap}
\alias{ap}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
iterator going through every possible interval
}
\description{
this iterator will go through every interval [i,j], i<j
}
\usage{
ap(M, ds = 1)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{M}{
the data-structure to go through
}
  \item{ds}{
the dimension to explore
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
\code{\link{dx}}, \code{\link{Idx}}, \code{\link{win}}
}
\examples{
x <- rnorm(10); names(x) <- paste('e',1:10,sep='_')
print(x)
lambda( sum, x, ap )
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
\keyword{ ~kwd1 }
\keyword{ ~kwd2 }% __ONLY ONE__ keyword per line
