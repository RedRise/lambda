\name{lambda-package}
\alias{lambda-package}
\docType{package}
\title{
Apply a function over subparts of a big data structure.
}
\description{
Apply a function over subparts of a big data structure.
Typical applications are: rolling/expanding windows.
Default data structure [list of [list of [...]]] arrays.
}
\details{
\tabular{ll}{
Package: \tab lambda\cr
Type: \tab Package\cr
Version: \tab 1.0\cr
Date: \tab 2012-01-11\cr
License: \tab GPL-3\cr
LazyLoad: \tab yes\cr
}
lambda( sum, matrix(1:100,20,5), 2 )
lambda(  sd, matrix(1:100,20,5), Idx )
lambda(  sd, matrix(1:100,20,5), list(dx,win(3)) )
}
\author{
EONOS INVESTMENT TECHNOLOGIES
Maintainer: Who to complain to <guillaume.garchery@gmail.com>
}
\references{
~~ Literature or other references for background information ~~
}
\examples{
lambda( sum, matrix(rnorm(20),4,5), 1 )
}
