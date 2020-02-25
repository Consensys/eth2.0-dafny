
/** Helper types.  */
module Helpers {

    /** Try type (as in Scala). */
    datatype Try<T> = Success(t : T) | Failure 

    /* Option type */
    datatype Option<T> = None | Some(T)

    /* Either type */
    datatype Either<T> = Left(T) | Right(T)

}