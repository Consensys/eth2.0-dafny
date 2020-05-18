using System;
using System.Numerics;
using System.Diagnostics;
using System.IO;

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
 
using System.Text;

namespace thirdpartymerkleisation
{
    public partial class __default {
        public static Dafny.Sequence<byte>  BitlistRoot(Dafny.Sequence<bool> bitlist, Dafny.Sequence<byte> bitlistInBytes, BigInteger limit)
        {
                string bl = "";
                for(int i = 0; i<bitlist.Elements.Length;i++)
                {
                    if(bitlist.Elements[i])
                    {
                        bl +="1";
                    }
                    else
                    {
                        bl+="0";
                    }
                }
                // Console.Write(bl);
                ProcessStartInfo start = new ProcessStartInfo();
                start.FileName = "python3";
                start.Arguments="PySszBitlistMerkleisation.py" + " " + bl;
                start.UseShellExecute = false;
                start.RedirectStandardOutput = true;

                Process cmdProcess = new Process();
                cmdProcess.EnableRaisingEvents = true;
                cmdProcess.StartInfo = start;
                cmdProcess.Start();                

                var br = new BinaryReader(cmdProcess.StandardOutput.BaseStream);
                byte[] retBytes = br.ReadBytes(32);
                // Console.Write("\n            " + Encoding.Default.GetString(retBytes));
                return Dafny.Sequence<byte>.FromElements(retBytes);
        }
    }
}