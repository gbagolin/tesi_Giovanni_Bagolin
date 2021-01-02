import './App.css';
import React, { useState } from 'react';
import Navbar from './Navbar'
import Title from './Title'
import Button from './Button'
import Modal from './Modal'

function App() {
  return (
    <>
      <div className="container-fluid">
        <main>
          <Title />
          <Button />
          <Modal />
        </main>
      </div>
    </>
  )
}

export default App;
