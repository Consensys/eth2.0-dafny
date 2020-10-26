#! /bin/bash
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

error=0
processeddirs=0

# help and usage
help()
{
   # Display Help
   echo "Usage: $0 dir, where dirname is the folder you want to check."
   echo "All .dfy files in the folder dirname will be checked."
   echo
}

# Check number of arguments
if  [ "$#" -ne 1 ];  
    then 
    echo "Illegal number of parameters"
    help
    exit 1
fi

if [ ! -d "$1" ] 
then
    echo -e "${RED}Error: Root directory $1 DOES NOT exists.${NC}" 
    exit 2 
fi

# The list of dirs 
listofdirs=`ls -d $1/*/`
for dir in $listofdirs "$1"
do
    echo "Processing " $dir
    ./verifyAll.sh $dir
    if [ $? -eq 0 ] # check if errors
    then
      echo -e "${GREEN}No errors in directory $dir${NC}"
    else
      echo -e "${RED}Some errors occured in directory $dir${NC}"
      error=$((error + 1))
    fi
done

if [ $error -ne 0 ]
then
  echo -e "${RED}Some directories [$error/$processeddirs] has(ve) errors :-("
  exit 1
else 
  echo -e "${GREEN}No errors in any dirs! Great job.${NC}"
  exit 0
fi
