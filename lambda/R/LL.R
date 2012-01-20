#==============================================================================
#   UTILITY FUNCTION
#==============================================================================
#.l      <- list
..rev = function(x) x[length(x):1]; .rev = function(x, ...) .L(..rev, x, ...)
..na <- function(x, fwd = TRUE, fill = NULL, evac = c(NA, NaN, Inf, -Inf))  { 
x[x %in% evac] <- NA; if (!is.null(fill)) return(replace(x, is.na(x), fill)) else {if(!fwd) x <- ..rev(x);ans <- x[c(NA, which(ii<-!is.na(x)))[cumsum(ii) + 1]]; names(ans) <- names(x);if(fwd) ans else ..rev(ans) } }
.na = function(x, fwd = TRUE, fill = NULL, ds = 2, ...) lambda(..na, lambda(..na, x , ds = ds, ... ,fwd = fwd, fill = fill), ds = ds,..., if (fwd) FALSE else TRUE, fill = fill)
..cumsum = function(x) cumsum(..na(x,fill = 0)); .cumsum = .cs = function(x, ...) lambda(..cumsum, x, ...)
.dup    <- function( X, fill=NA ){
    if (is.recursive(X)){ 
        res<-lapply( X, .dup, fill); names(res)<-names(X); res 
    } else { 
        array( fill, .dim(X), .dimnames(X) ) 
    }
}
.dim    <- function(M, nona = FALSE){ 
    if (nona) M <- M[which(!is.na(M))]; 
    if (is.recursive(M)){ 
        c( length(M), .dim(M[[1]]) ) 
    } else { 
        if (is.vector(M)) length(M) else dim(M) 
    } 
}
.dimnames   <- function(M){ 
    if (is.recursive(M)){ 
        tp.<-names(M); c( list(tp.), .dimnames(M[[1]]) ) 
    } else { 
        if (is.vector(M)) list(names(M)) else dimnames(M) 
    }
}

#==============================================================================
#   WRAPPERS
#==============================================================================
.wNULL <- function(fun) function(...) if (is.null(list(...)[[1]])) NULL else fun(...)
.wL    <- function(fun,...) function(argaslist) do.call( fun, c( argaslist, list(...)) )
.wD    <- function(fun)     function(...) drop(fun(...))
.w2L = function( fun = .nthg, optargs = NULL , type = 0){ 
            function(...){
                X <- list(...)[[1]]
                if ( px<-!isdx(X) ) X <- .dlog(X) 
                res <- .am(1 + .cs( do.call( fun, c( list(X), list(...)[-1], optargs ) )))
                return(res)
            }
}
#.wi <- function( fun, ds, ..., struct=TRUE) function(M) .ii( fun, M, ds, ..., struct=struct )
.wPCA <- function( FUN, cov='.Scov' ){
    function( M, ... ){
        V<- eigen( match.fun(cov)(M) )$vectors ; try(dimnames(V) <- list(colnames(M), colnames(M)), silent = TRUE)
        res  <- list(match.fun(FUN),  M %*%V)  %*% t(V); res }}
#==============================================================================
#   SELECTION FUNCTION
#==============================================================================

.get <- function( M, ix=if (is.list(M)) TRUE else as.list(rep(TRUE,length(.dim(M))))){
# extract sub-manifold from multidimensional manifold
# sample call: .get( diag(10), list(1:5,3:7) ); .get( diag(10), list(TRUE,1) )
    if (is.null(ix[[1]])){ return(NULL) }#return(M)
    if (!is.recursive(M)){
       # print( parse(text=paste("M[",paste(ix,collapse=','),",drop=FALSE]",sep="")))
       ix  <- lapply( ix, function(j) if (is.call(j)) j else paste('c(',paste(j,collapse=','),')') )
       res <- eval(parse(text=paste("M[",paste(ix,collapse=','),",drop=FALSE]",sep="")))
       #print( paste('M[',paste(lapply( ix, function(x) paste('c(',paste(x,collapse=','),')')),collapse=','),',drop=FALSE]',collapse=',') )
       #res <- eval(  parse( text= paste('M[',paste(lapply( ix, function(x) paste('c(',paste(x,collapse=','),')')),collapse=','),',drop=FALSE]',collapse=',')) )
    } else {
        # res <- if (length(ix[[1]])==1) .get( M[[ ix[[1]] ]], ix[-1] ) else lapply( .Internal(do.call('[',c(list(M),ix[1]), parent.frame())), function(m) .get( m, ix[-1] ) ) 
        res <- if (length(ix)==1) M[ix] else lapply( M[ix[[1]]], function(m) .get( m, ix[-1] ) ) 
    }
    return(res)
}
.get <- function( M, ix=if (is.list(M)) TRUE else as.list(rep(TRUE,length(.dim(M))))){
    # print(ix)
    if (is.null(ix[[1]])){ return(NULL) }#return(M)
    if (!is.recursive(M)){
        res <- .Internal(do.call( '[', c(list(M),ix,drop=FALSE), parent.frame()))
    } else {
        # res <- if (length(ix[[1]])==1) .get( M[[ ix[[1]] ]], ix[-1] ) else lapply( .Internal(do.call('[',c(list(M),ix[1]), parent.frame())), function(m) .get( m, ix[-1] ) ) 
        res <- if (length(ix)==1) M[ix] else lapply( M[ix[[1]]], function(m) .get( m, ix[-1] ) ) 
    }
return(res)}# SELECTION FUNCTION


#==============================================================================
#   MONO  DIMENSION ITERATORS
#==============================================================================
.trv     <- function( M, ds=1 ){ expr.l<-list(TRUE); return( list( 'expr.l'=expr.l, 'glob.sz'=1, 'glob.n'=tail(.dimnames(M)[ds][[1]],1), 'cast.ix'=NULL) ) } 
.warg    <- function(fun,...){ 
            as.<-formals(fun); as.[match(names(list(...)),names(as.))]<-list(...)
            do.call( as.function.default, list( append( as., body(fun)), envir=parent.frame()) )} 

# rn : marginal dimname
# len: length of rn
# stp: stp of progression
# pvt: index or name that should appear in progression    
..seq <- function( from, to, stp=1, pvt=1, rn=NULL ){
    if (stp!=1) {
        ix <- if (class(pvt)!="numeric"){ match( as.character(pvt), rn ) } else { if (pvt<0) to+pvt+1 else pvt }
        if (is.na(ix)) ix <- 1
        mv <- (ix-from) %% stp; seq.int( from, to-mv, stp ) + mv
    } else { seq.int( from, to, 1 ) }
}

dx      <- function( M, ds=1, stp=1, pvt=1, rsz=TRUE ){
            if ( missing(M) ) return( .warg(dx,stp=stp,pvt=pvt,rsz=rsz) )
            dn <- .dimnames(M)[ds][[1]]
            expr.l<- as.list(six<-..seq( 1, Md<-.dim(M)[ds], stp, pvt, dn )); if (rsz){ gn<-dn } else { gn<-dn[six]; six<-NULL }
            return( list( 'expr.l'=expr.l, 'glob.sz'=Md, 'glob.n'=gn, 'cast.ix'=six) ) }

Idx     <- function( M, ds=1, stp=1, pvt=1, rsz=TRUE ){ 
            if ( missing(M) ) return( .warg(Idx,stp=stp,pvt=pvt,rsz=rsz) )
            dn <- .dimnames(M)[ds][[1]]
            expr.l<-lapply( six<-..seq( 1, Md<-.dim(M)[ds], stp, pvt, dn ), function(i) substitute(seq_len(i),list(i=i))); if (rsz){ gn<-dn } else { gn<-dn[six]; six<-NULL }
            return( list( 'expr.l'=expr.l, 'glob.sz'=if (rsz) Md else length(expr.l), 'glob.n'=gn, 'cast.ix'=six) ) }

win     <- function( w=NULL, stp=1, pvt=1, rsz=TRUE ) if (is.null(w)){ .warg(Idx,stp=stp,pvt=pvt,rsz=rsz) } else if (w==1){ .warg(dx,stp=stp,pvt=pvt,rsz=rsz) } else { .warg(.win,w=w,stp=stp,pvt=pvt,rsz=rsz) }

.win   <- function( M, ds=1, w, stp=1, pvt=1, rsz=TRUE ){ 
    w    <- min(w, Md<-.dim(M)[ds]); dn <- .dimnames(M)[ds][[1]]
    expr.l  <- lapply( cast.ix<-..seq( w, Md, stp, pvt, dn ), function(i) substitute(seq.int(a,b,1),list(a=i-w+1,b=i)) )
    if (rsz) return( list( 'expr.l'=expr.l, 'glob.sz'= Md, 'glob.n'= dn , 'cast.ix'=cast.ix) )
    return( list( 'expr.l'=expr.l, 'glob.sz'= length(expr.l), 'glob.n'= dn[cast.ix], 'cast.ix'=NULL) )     }

exc <- function(x,ds=1,up=TRUE){
    if (missing(x)) return( .warg(exc,up=up) )
    if(!up) x<--x; cix<-list(); a<-NULL; cs<-0;
    for (i in seq_len(length(x)->lx)){
        v<-x[i]; cs<-cs+v; if (v<0){ if (is.null(a)){ a<-i; cs<-v } } else { if (cs>0 & !is.null(a)){ cix[[length(cix)+1]]<-list(a,i-1);cs<-0;a<-NULL }}}
    if (!is.null(a)) cix[[length(cix)+1]] <- list(a,lx); 
    if (length(cix)==0){ expr.l<-list(NULL); glob.n<-names(x)[[length(x)]]} else {
        dn.<- names(x)
        expr.l <- .Internal(unlist(lapply(cix, function(ii) substitute(seq(a,b),list(a=ii[[1]],b=ii[[2]]))),FALSE,FALSE))
        glob.n <- if (is.null(dn.)) NULL else .Internal(unlist(lapply(cix, function(ii) paste(dn.[ii[[1]]],dn.[ii[[2]]])),FALSE,FALSE)) }
    return( list( 'expr.l'=expr.l, 'glob.sz'=length(cix) , 'glob.n'=glob.n, 'cast.ix'=NULL) )}

ap      <- function( M, ds=1 ){ tp.<-combn(.dim(M)[ds],2,FUN=function(x) substitute(seq(a,b),list(a=x[1],b=x[2])), simplify=FALSE); 
                                 dn.<-.dimnames(M)[ds][[1]]; 
                                 glob.n <- if (is.null(dn.)) NULL else .Internal(unlist(lapply(tp., function(x) paste(dn.[x[[2]]],dn.[x[[3]]])),FALSE,FALSE)); 
                                 return( list('expr.l'=tp., 'glob.sz'=length(tp.), 'glob.n'=glob.n, 'cast.ix'=NULL)) }
#==============================================================================
#  MONO ITERATOR HANDLER
#==============================================================================
.x      <- function( iters ){
    function( M, struct=TRUE ){ 
        il    <- lapply( seq_len(length(.dim(M))), 
                    function(i) (if (i>length(iters)) .trv else if (is.null(iters[[i]])) .trv else iters[[i]])(M,i) )
        lil   <- seq_len(length(il))
        f.arg <- .Internal(do.call(expand.grid, c(lapply(il,function(x) seq_len(length(x$expr.l))), c(KEEP.OUT.ATTRS=FALSE, stringsAsFactors=FALSE)),parent.frame()))

        list(   'l.n'   = nrow(f.arg),
                'a.d'   = if ( k1<-(length(rd<-(d<-.Internal(unlist(lapply(il,function(x) x$glob.sz),FALSE,FALSE)))[d>1]) == 0) ) 1 else rd , 
                'a.dn'  = if (k1){ list(il[[1]]$glob.n) } else{ lapply(which(d>1),function(i) il[[i]]$glob.n )},
                'cast'  = if (all(.Internal(unlist(lapply(lc<-lapply(il,function(x) x$cast.ix),is.null),FALSE,FALSE)))){ NULL } else { lapply(which(d>1),function(i){ if (is.null(lc[[i]])) seq_len(il[[i]]$glob.sz) else lc[[i]] } )} ,
                'f'     = if (struct){ 
                            function ( i ){ aix<-as.integer(f.arg[i,]);     .get(M,lapply( lil, function(j){ il[[j]]$expr.l[[ aix[j] ]] }))}
                          } else {
                            function ( i ){ aix<-as.integer(f.arg[i,]); unlist(as.vector(.get(M,lapply( lil, function(j){ il[[j]]$expr.l[[ aix[j] ]] }))))}
                          } )
        }
}

# .i VERSION *** 2011-04-08 ***
#   +++ optional devs:  what is is.list(M) and ds[[1]] == dx, should we pass an lapply first? (depends if iterators ars independent or not)
#                       do we need to return a structure that looks like M? M is list x array x array and ds = dx x XX x YY

lambda <-  function( fun, M, ds=if(is.list(M)){1}else{if (is.matrix(M))2 else NULL}, ..., struct=TRUE, simp=TRUE ){ 

        if (!is.list(ds)){ ds <- if (is.numeric(ds)){ if (identical(ds,0)){list(NULL)}else{ tp.<-rep(list(NULL),max(ds));tp.[ds]<-list(dx); tp.}} else{ list(ds)} }
        ds   <- ds[ 1:min(length(ds), length(.dim(M))) ]  # be sure to have less ds than .dim(M)
        nds  <- .Internal(unlist(lapply(ds,is.null),FALSE,FALSE)); isdx <- .Internal(unlist(lapply(ds,identical,dx),FALSE,FALSE))

        if (all(nds)){ 
            if (is.list(M)){ res <- Reduce( fun, M, ... )} else { res <- .Internal(do.call(fun,list(M,...),parent.frame())) }
        } else if (is.list(M) && identical(ds[[1]],dx) ){ 
            if (all(nds[-1])){
                res <- lapply( M, function(Melmt) if (struct) fun(Melmt,...) else fun(as.vector(Melmt),...) )
            } else {
                res <- lapply( M, function(Melmt) lambda( fun, Melmt, ds[-1], ..., struct=struct ) )
                if (simp) res <- .l2a( res, length(res), list(names(M)) )
            }

        } else if (is.array(M) && sum(isdx)>0) { 
            if (all(nds[-(wisdx<-which(isdx))])){
                res <- .apply( M, wisdx, function(Melmt){
                        if (!struct){
                            if (is.list(Melmt)){ 
                                fun(unlist(Melmt),...)
                            } else {
                                fun(as.vector(Melmt),...)
                            }
                        } else {
                                fun(Melmt,...)
                        }
                        })
            } else {
                dxd <- which( rd <- isdx[which(!nds)]); fo <- order(c( dxd, seq_len(lrd<-length(rd))[-dxd]))
                res <- .apply( M, wisdx, function(x) lambda( fun, x, ds[-wisdx], ..., struct=struct ), simp )

                if (is.recursive(res)){
                    res <- lapply( res, function(x) .Internal(aperm( x, c( fo, if (lrd==(ldx<-length(dim(x)))) NULL else (lrd+1):ldx), TRUE)) )
                } else {
                    res <- .Internal(aperm( res, c( fo, if (lrd==(ldx<-length(dim(res)))) NULL else (lrd+1):ldx), TRUE ) )
                }
            }
        } else {
            tpfun   <- .wNULL(fun); path  <- .x(ds)(M,struct)
            res     <- lapply( seq_len(path$l.n), function(i) tpfun( path$f(i), ...  ) )
            if (simp) res     <- .l2a( res, path$a.d, path$a.dn, path$cast )
        }
        if (is.matrix(M) && is.matrix(res) && nds[1] && !(is.na(nds[2]) || nds[2]) ) res <- t(res)
return(res)}

#==============================================================================
#   APPLY RECODED
#==============================================================================
.apply <- function( X, MARGIN, FUN, ..., simp=TRUE){

    if (is.vector(X)){  X <- array( X, length(X), list(names(X)) ); MARGIN <- 1 }
    d <- dim(X); dl<-length(d); ds<-seq_len(dl); dn <- dimnames(X); if (dl==1) MARGIN<-1
    s.call  <- ds[-MARGIN]; s.ans  <- ds[MARGIN]
    d.call  <-  d[-MARGIN]; d.ans  <-  d[MARGIN]
    dn.call <- dn[-MARGIN]; dn.ans <- dn[MARGIN]
    d2      <- prod(d.ans)
    if (length(MARGIN)==1 && dl==2){
        if ( MARGIN==1 ){
           ans  <- lapply( seq_len(d2), function(i) FUN(X[i,,drop=TRUE]) )
        } else {
            ans <- lapply( seq_len(d2), function(i) FUN(X[,i,drop=TRUE]) )
        }
    } else {
        if (!identical(c(s.ans, s.call),ds)) X <- .Internal(aperm( X, c(s.ans, s.call),TRUE))
        dim(X)   <- c(d2, prod(d.call))
        ans <- lapply( seq_len(d2), function(i) FUN(array(X[i,],d.call,dn.call),...) )
    }    
    if (simp) ans <- .l2a(ans,d.ans,dn.ans)
return(ans)}

#   +++ future dev, add a all(ans.nnull) case
#
.l2a <- function( ans, ini.d=length(ans), ini.dn=NULL, cast=NULL ){

    i <- 1; first<-TRUE; ans.l <- length(ans)
    for ( k in seq_len(ans.l) ){
        if (is.null(ans[[k]])) if (first){ ans[[k]]<-ans.tmp <- .dup(ans[[i]]); first<-FALSE } else { ans[[k]] <- ans.tmp }
    }

    ans.islist  <- is.recursive( ans[[i]] )
    ans.struct  <- .dim( ans[[ i ]] ); ans.struct.len <- prod(ans.struct)
    ans.dn      <- .dimnames( ans[[ i ]] ); if (is.null(ans.dn)) ans.dn <- list(ans.dn)

    if ( ans.islist ){
        ans <- lapply( seq_len(ans.struct[1]), function(i) .l2a( lapply(ans, function(ans.one) ans.one[[i]] ), ini.d=ini.d, ini.dn=ini.dn, cast=cast ) ) 
        names(ans) <- ans.dn[[1]]
        return(ans)
    } else {
        if (nc<-is.null(cast)){
            ans.d <- if (ans.struct.len==1) ini.d else c(ans.struct, ini.d)
        } else {
            sub.d <- .Internal(unlist(lapply(cast,length),FALSE,FALSE))
            ans.d <- if (ans.struct.len==1) sub.d else c(ans.struct, sub.d)
        }

        ans <- array( .Internal(unlist(ans,FALSE,FALSE)), dim= ans.d )
        if ( ans.struct.len > 1 ) ans <- .Internal(aperm( ans, c( (length(ans.struct)+1):length(ans.d), seq_len(length(ans.struct)) ), TRUE )) 

        if (!nc){
            res.d <- c(ini.d, dim(ans)[-seq_len(length(ini.d))] )
            res   <- array( NA, dim=res.d, dimnames = if (ans.struct.len==1) ini.dn else append( ini.dn, ans.dn ) )
            cast  <- lapply( seq_len(length(res.d)), function(i) if (is.null(cast[i][[1]])) seq_len(res.d[i]) else cast[[i]] )
            return(do.call( '[<-', c(list(res),cast,list(ans)) ))
        } else { 
            dimnames(ans) <- if (ans.struct.len==1) ini.dn else append( ini.dn, ans.dn ) 
            return(ans)
        }
    }
}

