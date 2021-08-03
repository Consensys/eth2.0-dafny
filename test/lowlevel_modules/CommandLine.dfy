/*
 * Copyright 2021 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may 
 * not use this file except in compliance with the License. You may obtain 
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT 
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the 
 * License for the specific language governing permissions and limitations 
 * under the License.
 */

include "../../src/dafny/utils/NativeTypes.dfy"
include "../../src/dafny/utils/Helpers.dfy"
//include "CommandLineLowLevel.dfy"


module {:extern "commandline"} CommandLineLowLevel
{
    class {:extern} Dummy {
        
    } 
    
    import opened NativeTypes

    function method {:extern} GetNumComandLineParamters():  nat 

    function method {:extern} GetCommandLineParamter(i:nat): string
    requires i < GetNumComandLineParamters()

}
// module CommandLine 
// {
    // import opened Helpers
    // import opened CommandLineLowLevel
    function method GetCommandLineParamters(): seq<string>
    ensures |GetCommandLineParamters()| == CommandLineLowLevel.GetNumComandLineParamters()
    ensures forall i | 0 <= i < |GetCommandLineParamters()| :: GetCommandLineParamters()[i] ==  CommandLineLowLevel.GetCommandLineParamter(i)
    {
        Helpers.initSeq<string>((i:nat) requires i < CommandLineLowLevel.GetNumComandLineParamters() => CommandLineLowLevel.GetCommandLineParamter(i), CommandLineLowLevel.GetNumComandLineParamters())
    }
// }