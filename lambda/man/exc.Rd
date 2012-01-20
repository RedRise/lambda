\name{exc}
\alias{exc}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
monodimensional iterator going through negative sum windows.
}
\description{
this iterator will consider all windows [i:(i+k)] where
all sum(x[i:(i+l)]) with l<=k are negative. Could only be
applied on numerical vectors.
}
\usage{
exc(x, ds = 1, up = TRUE)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{x}{
numerical vector.
}
  \item{ds}{
not used in this particular iterator.
}
  \item{up}{
boolean, default TRUE. If FALSE, behave as if -x was the input. 
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
\code{\link{dx}},\code{\link{Idx}}, \code{\link{win}}, \code{\link{ap}}
}
\examples{
## exc can only be applied on numerical vectors
x 	 <- c(1,-1,0.5,1,1,-1,-1,-1,2,2,-2,-2,1,1,1,1,1,1)
names(x) <- paste('day',1:length(x),sep='_')

## observe the sub-parts of this numerical vector through 'exc'
lambda( identity, x, exc, simp=0 )

## computing min element on every period
lambda( min, x, exc )

}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
\keyword{ ~kwd1 }
\keyword{ ~kwd2 }% __ONLY ONE__ keyword per line
