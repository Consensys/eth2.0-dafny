/*
 * Copyright 2020 ConsenSys AG.
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

using System;
using System.Numerics;

namespace commandline
{
    public partial class __default {
        public static BigInteger GetNumComandLineParamters()
        {
            return System.Environment.GetCommandLineArgs().Length;
        }

        public static Dafny.Sequence<char> GetCommandLineParamter(BigInteger i)
        {
            return Dafny.Sequence<char>.FromElements(System.Environment.GetCommandLineArgs()[(ulong)i].ToCharArray());
        }        
    }
    
}