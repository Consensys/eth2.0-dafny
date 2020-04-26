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

module MathDivR {
    lemma LemmaConverseRealDiv(a:real,b:real,c:real)
    requires b != 0.0
    requires a == b *c
    ensures c == a/b;
    {}    

    lemma LemmaRealSumDistributeOverDiv(a:real,b:real,c:real)
    requires c!= 0.0
    ensures (a+b)/c == a/c + b/c 
    {}

    lemma LemmaRealSubDistributeOverDiv(a:real,b:real,c:real)
    requires c!= 0.0
    ensures (a-b)/c == a/c - b/c 
    {}

}